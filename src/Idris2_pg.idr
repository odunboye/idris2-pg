module Idris2_pg

import Data.IORef
import Data.List
import Data.Maybe
import Data.PGTypes
import Data.PGValue
import Helper
import Network.Core
import Network.RawSocket
import Network.Timeout
import Derive.Prelude

-- Bounds a connect-shaped operation (connectDB's own TCP-connect-plus-auth,
-- or cancelQuery's fresh out-of-band connection) by cfg's connectTimeoutMs,
-- if set - see Network.Timeout for what "bounds" does and doesn't mean.
withConnectTimeout : PGConfig -> IO (Either PGError a) -> IO (Either PGError a)
withConnectTimeout cfg action = case connectTimeoutMs cfg of
     Nothing => action
     Just ms => do
       res <- withTimeout ms action
       pure (fromMaybe (Left (ConnectionError "connection timed out")) res)

-- Bounds a single wire round-trip (a query, a COPY, a notification wait) by
-- db's readTimeoutMs, if set.
withReadTimeout : DB -> IO (Either PGError a) -> IO (Either PGError a)
withReadTimeout db action = case readTimeoutMs (cfg db) of
     Nothing => action
     Just ms => do
       res <- withTimeout ms action
       pure (fromMaybe (Left (ConnectionError "operation timed out waiting for the server")) res)

public export
connectDB : PGConfig -> IO (Either PGError DB)
connectDB cfg = withConnectTimeout cfg $ do
  conn <- connectPG (host cfg) (port cfg) (useTLS cfg)
  case conn of
       Left err => pure (Left (ConnectionError err))
       (Right pgConn) => do
         let startupMsg = encode (StartupMsg 3 [("user", user cfg), ("database", database cfg)])
         spgConn <- sendStartup pgConn startupMsg
         case spgConn of
              Nothing => pure (Left (ConnectionError "Error sending StartupMsg"))
              (Just x) => do
                let conx = mkConnectedPG x
                res <- handleStartupResponse (user cfg) (password cfg) conx
                case res of
                     Left err => pure (Left err)
                     Right sr => case errors sr of
                                      (e :: _) => pure (Left (SqlError e))
                                      []       => do
                                        ref <- newIORef (map status (ready sr))
                                        cache <- newIORef []
                                        counter <- newIORef 0
                                        pure (Right (MkDB conx (Just sr) cfg ref cache counter))

-- Records the transaction status from a batch's final ReadyForQuery (the
-- last result's, since a multi-statement batch shares one at the end) so
-- txStatus can report it without a round-trip.
noteStatus : DB -> List QueryResult -> IO ()
noteStatus db results = case reverse results of
     []       => pure ()
     (qr :: _) => case status qr of
                       Nothing                  => pure ()
                       Just (MkReadyForQuery s) => writeIORef (txState db) (Just s)

queryDB : DB -> String -> IO (Either PGError (List QueryResult))
queryDB db str = withReadTimeout db $ do
  let queryFrame = encode (QueryMsg (MkQuery str))
  resp <- pgSend (conn db) queryFrame
  case resp of
       (Left x) => pure (Left (ConnectionError x))
       (Right x) => do
         res <- handleQueryResponses db
         case res of
              Right results => noteStatus db results
              Left _        => pure ()
         pure res

-- Runs a query via the extended protocol (Parse/Bind/Describe/Execute/Sync)
-- with text-encoded parameters, so caller-supplied values never need to be
-- escaped/interpolated into the SQL string. Postgres only allows a single
-- statement per Parse, so this always yields one result.
--
-- The Parse step is skipped for a query text already prepared earlier on
-- this connection (see DB.stmtCache) - a named statement persists for the
-- life of the session, so this is safe to reuse across calls. A statement
-- is cached only after a fully clean first run, and evicted on any error
-- (whether that error is because the SQL was actually bad, in which case
-- it was never cached to begin with, or because something upstream of the
-- statement itself changed) so a bad cache entry never sticks around - at
-- worst that just costs an extra re-Parse next time, same as no caching.
execParams : DB -> String -> List (Maybe String) -> Bool -> IO (Either PGError (List QueryResult))
execParams db query params wantBinary = do
  cache <- readIORef (stmtCache db)
  case lookup query cache of
       Just stmtName => runPrepared stmtName False
       Nothing => do
         n <- readIORef (stmtCounter db)
         writeIORef (stmtCounter db) (n + 1)
         runPrepared ("idris2pg_stmt_" ++ show n) True
  where
    dropCached : IO ()
    dropCached = modifyIORef (stmtCache db) (filter (\(k, _) => k /= query))

    cacheStmt : String -> IO ()
    cacheStmt stmtName = modifyIORef (stmtCache db) ((query, stmtName) ::)

    runPrepared : String -> Bool -> IO (Either PGError (List QueryResult))
    runPrepared stmtName isNew = withReadTimeout db $ do
      let bindParams = map (map stringToBytes) params
          parseFrame = if isNew then encode (Parse stmtName query []) else []
          frame = parseFrame
                    ++ encode (Bind "" stmtName bindParams wantBinary)
                    ++ encode (Describe 'P' "")
                    ++ encode (Execute "" 0)
                    ++ encode Sync
      resp <- pgSend (conn db) frame
      case resp of
           Left x => do
             dropCached
             pure (Left (ConnectionError x))
           Right () => do
             res <- handleQueryResponses db
             case res of
                  Right results => do
                    noteStatus db results
                    let hasError = any (\qr => case errors qr of [] => False; _ => True) results
                    if hasError
                       then dropCached
                       else when isNew (cacheStmt stmtName)
                  Left _ => dropCached
             pure res


-- Runs a query, choosing the simple protocol (always text) for zero-param,
-- text-format requests, and the extended protocol otherwise - the simple
-- protocol has no way to request binary results at all.
runQuery : DB -> String -> List (Maybe String) -> Bool -> IO (Either PGError (List QueryResult))
runQuery db stmt [] False = queryDB db stmt
runQuery db stmt params wantBinary = execParams db stmt params wantBinary

-- execCommand/queryRows are single-statement APIs; a ';'-separated batch
-- would otherwise have its results silently merged/corrupted, so this
-- rejects anything other than exactly one result with a clear error instead.
singleResult : List QueryResult -> Either PGError QueryResult
singleResult [qr] = Right qr
singleResult []   = Left (ProtocolError "no result returned for statement")
singleResult xs   = Left (ProtocolError
  ("expected exactly one statement's result, got " ++ show (length xs) ++
   " - multi-statement SQL is not supported by execCommand/queryRows; use execMulti"))

collectErrors : QueryResult -> Either PGError QueryResult
collectErrors qr = case errors qr of
     (e :: _) => Left (SqlError e)
     []       => Right qr

||| Run an INSERT/UPDATE/DELETE/DDL statement. Returns the command tag
||| (e.g. "INSERT 0 1") on success.
public export
execCommand : DB -> String -> List (Maybe String) -> IO (Either PGError String)
execCommand db stmt params = do
  result <- runQuery db stmt params False
  pure (result >>= singleResult >>= collectErrors >>= \qr => Right (fromMaybe "" (commandTag qr)))

||| Run a SELECT and return the decoded rows, in text format (the default -
||| see "Value decoding" for what this covers).
public export
queryRows : DB -> String -> List (Maybe String) -> IO (Either PGError (List Row))
queryRows db stmt params = do
  result <- runQuery db stmt params False
  pure (result >>= singleResult >>= collectErrors >>= \qr => Right (toRows qr))

||| Like queryRows, but requests binary format for every result column.
||| Only getInt/getInteger/getBool/getDouble/getText understand binary
||| format (see their doc comments); the others (getDate/getTimestamp/
||| getArray*/getJSON) only support text and will fail clearly if used on
||| a binary-format column. Unlike text mode, a type mismatch here (e.g.
||| calling getDouble on a binary int4 column) is not guaranteed to fail
||| cleanly - binary formats don't self-describe their type the way text
||| does, so this is a "you must get the types right" opt-in, not a safer
||| default.
public export
queryRowsBinary : DB -> String -> List (Maybe String) -> IO (Either PGError (List Row))
queryRowsBinary db stmt params = do
  result <- runQuery db stmt params True
  pure (result >>= singleResult >>= collectErrors >>= \qr => Right (toRows qr))

||| Run a (possibly ';'-separated, multi-statement) batch via the simple
||| query protocol and get back one QueryResult per statement, in order.
||| Parameters aren't supported here (the extended protocol only ever runs
||| one statement per call) - use execCommand/queryRows for those.
public export
execMulti : DB -> String -> IO (Either PGError (List QueryResult))
execMulti db stmt = queryDB db stmt

||| The transaction status as of the last query run on this connection
||| (Idle/InTransaction/FailedTransaction), without needing a round-trip.
||| Nothing only before the first query completes.
public export
txStatus : DB -> IO (Maybe TxStatus)
txStatus db = readIORef (txState db)

public export
beginTx : DB -> IO (Either PGError String)
beginTx db = execCommand db "BEGIN" []

public export
commitTx : DB -> IO (Either PGError String)
commitTx db = execCommand db "COMMIT" []

public export
rollbackTx : DB -> IO (Either PGError String)
rollbackTx db = execCommand db "ROLLBACK" []

||| Runs `action` inside BEGIN/COMMIT, rolling back instead if it returns a
||| Left. Either way, `action`'s result is returned unchanged.
public export
withTransaction : DB -> IO (Either PGError a) -> IO (Either PGError a)
withTransaction db action = do
  _ <- beginTx db
  result <- action
  case result of
       Right _ => do _ <- commitTx db; pure result
       Left _  => do _ <- rollbackTx db; pure result

quoteIdent : String -> String
quoteIdent s = "\"" ++ pack (concatMap escapeChar (unpack s)) ++ "\""
  where
    escapeChar : Char -> List Char
    escapeChar '"' = ['"', '"']
    escapeChar c   = [c]

||| Starts listening for NOTIFY on `channel` on this connection. Use a
||| connection dedicated to listening - waitForNotification blocks it until
||| a notification arrives, so it can't run other queries meanwhile.
public export
listenChannel : DB -> String -> IO (Either PGError String)
listenChannel db channel = execCommand db ("LISTEN " ++ quoteIdent channel) []

public export
unlistenChannel : DB -> String -> IO (Either PGError String)
unlistenChannel db channel = execCommand db ("UNLISTEN " ++ quoteIdent channel) []

||| Blocks until a NOTIFY arrives on any channel this connection is
||| listening to (see listenChannel), skipping over any other asynchronous
||| message (a NoticeMsg, a ParameterStatus change) in between. Bounded by
||| DB.cfg's readTimeoutMs, if set (see Network.Timeout for what "bounded"
||| means); blocks indefinitely otherwise.
public export
waitForNotification : DB -> IO (Either PGError Notification)
waitForNotification db = withReadTimeout db (go db)
  where
    go : DB -> IO (Either PGError Notification)
    go db = do
      frame <- readFrame (conn db)
      case frame of
           Left err                  => pure (Left (ConnectionError err))
           Right (NotificationMsg n) => pure (Right n)
           Right (ErrorMsg e)        => pure (Left (SqlError e))
           Right _                   => go db

||| Requests the server abort whatever this connection is currently running.
||| Per the Postgres protocol, cancellation is out-of-band: this opens a
||| fresh connection to send the CancelRequest on (no response is sent
||| either way, so success here just means the request was delivered).
public export
cancelQuery : DB -> IO (Either PGError ())
cancelQuery db = case map backendKey (result db) of
  Just (Just bk) => withConnectTimeout (cfg db) $ do
    conn <- connectPG (host (cfg db)) (port (cfg db)) (useTLS (cfg db))
    case conn of
         Left err => pure (Left (ConnectionError err))
         Right cancelConn => do
           sendRes <- pgSend cancelConn (encode (CancelRequest (pid bk) (secret bk)))
           _ <- close (MkConnected (socket cancelConn))
           case sendRes of
                Left err => pure (Left (ConnectionError err))
                Right () => pure (Right ())
  _ => pure (Left (ProtocolError "no backend key available"))

||| Runs a `COPY ... TO STDOUT` statement and returns the full copied data
||| (assumed text format - the default) as one String. Uses the simple
||| query protocol, same as any other unparameterized statement.
public export
copyOut : DB -> String -> IO (Either PGError String)
copyOut db sql = withReadTimeout db $ do
  resp <- pgSend (conn db) (encode (QueryMsg (MkQuery sql)))
  case resp of
       Left err => pure (Left (ConnectionError err))
       Right () => collect [] []
  where
    collect : List Bytes -> List Error -> IO (Either PGError String)
    collect chunks errs = do
      frame <- readFrame (conn db)
      case frame of
           Left err => pure (Left (ConnectionError err))
           Right (CopyData chunk)     => collect (chunk :: chunks) errs
           Right (ErrorMsg e)         => collect chunks (errs ++ [e])
           Right (ReadyForQueryMsg _) =>
             case errs of
                  (e :: _) => pure (Left (SqlError e))
                  []       => pure (Right (bytesToString (concat (reverse chunks))))
           Right _ => collect chunks errs  -- CopyOutResponse/CopyDone/CommandComplete/etc: keep reading

||| Runs a `COPY ... FROM STDIN` statement, sending `payload` (assumed
||| already formatted as text-format COPY data - tab-separated columns,
||| newline-separated rows) as a single CopyData message. Returns the
||| command tag (e.g. "COPY 3") on success.
public export
copyIn : DB -> String -> String -> IO (Either PGError String)
copyIn db sql payload = withReadTimeout db $ do
  resp <- pgSend (conn db) (encode (QueryMsg (MkQuery sql)))
  case resp of
       Left err => pure (Left (ConnectionError err))
       Right () => waitForCopyIn
  where
    finish : List Error -> Maybe String -> IO (Either PGError String)
    finish errs mTag = do
      frame <- readFrame (conn db)
      case frame of
           Left err => pure (Left (ConnectionError err))
           Right (ErrorMsg e)          => finish (errs ++ [e]) mTag
           Right (CommandCompleteMsg t) => finish errs (Just t)
           Right (ReadyForQueryMsg _) =>
             case errs of
                  (e :: _) => pure (Left (SqlError e))
                  []       => pure (Right (fromMaybe "" mTag))
           Right _ => finish errs mTag

    waitForCopyIn : IO (Either PGError String)
    waitForCopyIn = do
      frame <- readFrame (conn db)
      case frame of
           Left err => pure (Left (ConnectionError err))
           Right (CopyInResponseMsg _ _) => do
             sendRes <- pgSend (conn db)
                          (encode (CopyData (stringToBytes payload)) ++ encode CopyDone)
             case sendRes of
                  Left err => pure (Left (ConnectionError err))
                  Right () => finish [] Nothing
           Right (ErrorMsg e)         => finish [e] Nothing
           Right (ReadyForQueryMsg _) => pure (Left (ProtocolError "COPY FROM STDIN did not start (no CopyInResponse)"))
           Right _                    => waitForCopyIn

public export
closeDB : DB -> IO ()
closeDB (MkDB pgConn _ _ _ _ _) = do
  _ <- pgSend pgConn (encode Terminate)
  _ <- close (MkConnected (socket pgConn))
  pure ()
