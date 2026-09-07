module Idris2_pg

import Data.IORef
import Data.Maybe
import Data.PGTypes
import Data.PGValue
import Helper
import Network.Core
import Network.RawSocket
import Derive.Prelude

test : String
test = "Hello from Idris2!"

public export
record PGConfig where
  constructor MkPGConfig
  host     : String
  port     : Int
  user     : String
  password : String
  database : String

public export
connectDB : PGConfig -> IO (Either PGError DB)
connectDB cfg = do
  conn <- connectPG (host cfg) (port cfg)
  case conn of
       Nothing => pure (Left (ConnectionError "Could not connect"))
       (Just pgConn) => do
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
                                        pure (Right (MkDB conx (Just sr) ref))

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
queryDB db str = do
  let queryFrame = encode (QueryMsg (MkQuery str))
  resp <- send (MkConnected (socket (conn db))) queryFrame
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
-- escaped/interpolated into the SQL string. Uses an unnamed statement and
-- portal - no prepared-statement caching/reuse across calls. Postgres only
-- allows a single statement per Parse, so this always yields one result.
execParams : DB -> String -> List (Maybe String) -> IO (Either PGError (List QueryResult))
execParams db query params = do
  let bindParams = map (map stringToBytes) params
      frame = encode (Parse "" query [])
                ++ encode (Bind "" "" bindParams)
                ++ encode (Describe 'P' "")
                ++ encode (Execute "" 0)
                ++ encode Sync
  resp <- send (MkConnected (socket (conn db))) frame
  case resp of
       (Left x) => pure (Left (ConnectionError x))
       (Right x) => do
         res <- handleQueryResponses db
         case res of
              Right results => noteStatus db results
              Left _        => pure ()
         pure res


-- Runs a query, choosing the simple protocol for zero-arg statements (e.g.
-- DDL) and the extended protocol otherwise.
runQuery : DB -> String -> List (Maybe String) -> IO (Either PGError (List QueryResult))
runQuery db stmt [] = queryDB db stmt
runQuery db stmt params = execParams db stmt params

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
  result <- runQuery db stmt params
  pure (result >>= singleResult >>= collectErrors >>= \qr => Right (fromMaybe "" (commandTag qr)))

||| Run a SELECT and return the decoded rows.
public export
queryRows : DB -> String -> List (Maybe String) -> IO (Either PGError (List Row))
queryRows db stmt params = do
  result <- runQuery db stmt params
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

public export
closeDB : DB -> IO ()
closeDB (MkDB (MkPGConnection socket _) _ _) = do
  _ <- send (MkConnected socket) (encode Terminate)
  _ <- close (MkConnected socket)
  pure ()

testDrive : IO ()
testDrive = do
  let cfg = MkPGConfig "127.0.0.1" 5432 "root" "" "theideabankdb"
  db <- connectDB cfg
  case db of
       (Left err) => putStrLn (displayError err)
       (Right dbConn) => do
         _ <- showStartUpResult (result dbConn)
         some <- queryRows dbConn "select * from role" []
         case some of
              (Left err) => putStrLn (displayError err)
              (Right rows) => printLn rows
         closeDB dbConn
