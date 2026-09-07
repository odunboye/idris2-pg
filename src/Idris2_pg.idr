module Idris2_pg

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
connectDB : PGConfig -> IO (Either String DB)
connectDB cfg = do
  conn <- connectPG (host cfg) (port cfg)
  case conn of
       Nothing => pure (Left "Could not connect")
       (Just pgConn) => do
         let startupMsg = encode (StartupMsg 3 [("user", user cfg), ("database", database cfg)])
         spgConn <- sendStartup pgConn startupMsg
         case spgConn of
              Nothing => pure (Left "Error sending StartupMsg")
              (Just x) => do
                let conx = mkConnectedPG x
                res <- handleStartupResponse (user cfg) (password cfg) conx
                case errors res of
                     (e :: _) => pure (Left (message e))
                     []       => pure (Right (MkDB conx (Just res)))


queryDB : DB -> String -> IO (Either String QueryResult)
queryDB db str = do
  let queryFrame = encode (QueryMsg (MkQuery str))
  resp <- send (MkConnected (socket (conn db))) queryFrame
  case resp of
       (Left x) => pure (Left x)
       (Right x) => do
         res <- handleQueryResponse db
         pure (Right res )

-- Runs a query via the extended protocol (Parse/Bind/Describe/Execute/Sync)
-- with text-encoded parameters, so caller-supplied values never need to be
-- escaped/interpolated into the SQL string. Uses an unnamed statement and
-- portal - no prepared-statement caching/reuse across calls.
execParams : DB -> String -> List (Maybe String) -> IO (Either String QueryResult)
execParams db query params = do
  let bindParams = map (map stringToBytes) params
      frame = encode (Parse "" query [])
                ++ encode (Bind "" "" bindParams)
                ++ encode (Describe 'P' "")
                ++ encode (Execute "" 0)
                ++ encode Sync
  resp <- send (MkConnected (socket (conn db))) frame
  case resp of
       (Left x) => pure (Left x)
       (Right x) => do
         res <- handleQueryResponse db
         pure (Right res)


-- Runs a query, choosing the simple protocol for zero-arg statements (e.g.
-- DDL) and the extended protocol otherwise, then reports the first server
-- error (if any) as a Left instead of a "successful" empty result.
runQuery : DB -> String -> List (Maybe String) -> IO (Either String QueryResult)
runQuery db stmt [] = queryDB db stmt
runQuery db stmt params = execParams db stmt params

collectErrors : QueryResult -> Either String QueryResult
collectErrors qr = case errors qr of
     (e :: _) => Left (message e)
     []       => Right qr

||| Run an INSERT/UPDATE/DELETE/DDL statement. Returns the command tag
||| (e.g. "INSERT 0 1") on success.
public export
execCommand : DB -> String -> List (Maybe String) -> IO (Either String String)
execCommand db stmt params = do
  result <- runQuery db stmt params
  pure (result >>= collectErrors >>= \qr => Right (fromMaybe "" (commandTag qr)))

||| Run a SELECT and return the decoded rows.
public export
queryRows : DB -> String -> List (Maybe String) -> IO (Either String (List Row))
queryRows db stmt params = do
  result <- runQuery db stmt params
  pure (result >>= collectErrors >>= \qr => Right (toRows qr))

--closeDB
closeDB : DB -> IO ()
closeDB (MkDB (MkPGConnection socket _) _) = do
  _ <- send (MkConnected socket) (encode Terminate)
  _ <- close (MkConnected socket)
  pure ()

testDrive : IO ()
testDrive = do
  let cfg = MkPGConfig "127.0.0.1" 5432 "root" "" "theideabankdb"
  db <- connectDB cfg
  case db of
       (Left err) => putStrLn err
       (Right dbConn) => do
         _ <- showStartUpResult (result dbConn)
         some <- queryRows dbConn "select * from role" []
         case some of
              (Left err) => putStrLn err
              (Right rows) => printLn rows
         closeDB dbConn
