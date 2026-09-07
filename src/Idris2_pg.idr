module Idris2_pg

import Data.PGTypes
import Helper
import Network.Core
import Network.RawSocket
import Derive.Prelude

test : String
test = "Hello from Idris2!"

mkDB : String -> String -> String -> Int -> IO (Either String DB)
mkDB  user password db port= do
         conn <- connectPG "" port
         case conn of
              Nothing =>  pure (Left "Could not connect")
              (Just pgConn) => do
                let startuMsg = encode(StartupMsg 3 [("user", user), ("database", db)])
                spgConn <- sendStartup pgConn startuMsg
                case spgConn of
                     Nothing => pure (Left "Error sending StartupMsg")
                     (Just x) => do
                          let conx = (mkConnectedPG x)
                          res <- handleStartupResponse user password conx
                          pure (Right (MkDB conx (Just res)))


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


--closeDB
closeDB : DB -> IO ()
closeDB (MkDB (MkPGConnection socket _) _) = do
  _ <- send (MkConnected socket) (encode Terminate)
  _ <- close (MkConnected socket)
  pure ()

listTables : String
listTables = "SELECT tablename FROM pg_tables WHERE schemaname = 'public' AND tableowner <> 'postgres';"
                                                    


testDrive : IO ()
testDrive = do
  db <- mkDB "root" "" "theideabankdb" 5432
  case db of
       (Left err) => putStrLn err
       (Right dbConn) => do 
         --putStrLn (show dbConn)
         _ <- showStartUpResult (result dbConn)
         --some <- queryDB dbConn "select * from information_schema.tables"  
         some <- queryDB dbConn "select * from role"-- listTables --"select version()"
         case some of
              (Left err) => putStrLn err
              (Right x) => showQueryResult x
         closeDB dbConn
