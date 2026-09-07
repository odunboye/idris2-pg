module Main

import Data.IORef
import Data.Maybe
import Data.String
import System
import Idris2_pg
import Data.PGTypes
import Data.PGValue
import Helper
import Network.Core
import Network.RawSocket

-- CRUD smoke test against a real Postgres server. Connection details come
-- from environment variables so this isn't hardcoded to one local setup;
-- see README for how to point it at a disposable Postgres.
testConfig : IO PGConfig
testConfig = do
  host <- fromMaybe "127.0.0.1" <$> getEnv "PG_TEST_HOST"
  port <- fromMaybe 5432 . (>>= parsePositive) <$> getEnv "PG_TEST_PORT"
  user <- fromMaybe "testuser" <$> getEnv "PG_TEST_USER"
  password <- fromMaybe "testpass" <$> getEnv "PG_TEST_PASSWORD"
  database <- fromMaybe "testdb" <$> getEnv "PG_TEST_DB"
  pure (MkPGConfig host port user password database)

main : IO ()
main = do
  cfg <- testConfig
  Right db <- connectDB cfg
    | Left err => putStrLn ("FAIL connect: " ++ displayError err)
  putStrLn "OK connected"

  _ <- execCommand db "DROP TABLE IF EXISTS crud_demo" []

  Right _ <- execCommand db "CREATE TABLE crud_demo (id INT PRIMARY KEY, name TEXT)" []
    | Left err => putStrLn ("FAIL create table: " ++ displayError err)
  putStrLn "OK create table"

  Right tag1 <- execCommand db "INSERT INTO crud_demo (id, name) VALUES ($1, $2)" [Just "1", Just "Alice"]
    | Left err => putStrLn ("FAIL insert: " ++ displayError err)
  putStrLn ("OK insert: " ++ tag1)

  Right _ <- execCommand db "INSERT INTO crud_demo (id, name) VALUES ($1, $2)" [Just "2", Just "Bob"]
    | Left err => putStrLn ("FAIL insert 2: " ++ displayError err)

  Right rows <- queryRows db "SELECT id, name FROM crud_demo ORDER BY id" []
    | Left err => putStrLn ("FAIL select: " ++ displayError err)
  putStrLn ("OK select: " ++ show rows)

  Right tag3 <- execCommand db "UPDATE crud_demo SET name = $1 WHERE id = $2" [Just "Alicia", Just "1"]
    | Left err => putStrLn ("FAIL update: " ++ displayError err)
  putStrLn ("OK update: " ++ tag3)

  Right tag4 <- execCommand db "DELETE FROM crud_demo WHERE id = $1" [Just "2"]
    | Left err => putStrLn ("FAIL delete: " ++ displayError err)
  putStrLn ("OK delete: " ++ tag4)

  -- Regression test for the Phase 1 ErrorResponse decode fix: a malformed
  -- query must surface as a Left, not crash the process.
  badResult <- queryRows db "SELECT nonexistent_column FROM crud_demo" []
  case badResult of
       Left err => putStrLn ("OK graceful error on bad query: " ++ displayError err)
       Right _  => putStrLn "FAIL: malformed query did not report an error"

  -- Regression test for the Phase 0 short-read fix: round-trip a value large
  -- enough that the server's response can't arrive in a single TCP read.
  let bigString = pack (replicate 100000 'x')
  Right _ <- execCommand db "CREATE TABLE big_demo (val TEXT)" []
    | Left err => putStrLn ("FAIL create big table: " ++ displayError err)
  Right _ <- execCommand db "INSERT INTO big_demo (val) VALUES ($1)" [Just bigString]
    | Left err => putStrLn ("FAIL insert big value: " ++ displayError err)
  Right bigRows <- queryRows db "SELECT val FROM big_demo" []
    | Left err => putStrLn ("FAIL select big value: " ++ displayError err)
  case bigRows of
       [row] => case getText row "val" of
                     Right v => putStrLn ("OK large value round-trip, length matches: " ++ show (length v == 100000))
                     Left err => putStrLn ("FAIL decode big value: " ++ err)
       _ => putStrLn "FAIL: unexpected row count for big_demo"
  _ <- execCommand db "DROP TABLE big_demo" []

  Right _ <- execCommand db "DROP TABLE crud_demo" []
    | Left err => putStrLn ("FAIL final drop: " ++ displayError err)

  -- Regression test for the multi-statement result-merging fix: a
  -- ';'-separated batch must be rejected by the single-statement API...
  multiViaSingle <- execCommand db "SELECT 1; SELECT 2" []
  case multiViaSingle of
       Left (ProtocolError _) => putStrLn "OK execCommand rejects multi-statement SQL"
       Left err => putStrLn ("FAIL: wrong error for multi-statement SQL: " ++ displayError err)
       Right _  => putStrLn "FAIL: execCommand silently accepted multi-statement SQL"

  -- ...but must work correctly, as separate results, via execMulti.
  Right multiResults <- execMulti db "SELECT 1 AS n; SELECT 2 AS n"
    | Left err => putStrLn ("FAIL execMulti: " ++ displayError err)
  case map toRows multiResults of
       [[r1], [r2]] => case (getInt r1 "n", getInt r2 "n") of
                             (Right 1, Right 2) => putStrLn "OK execMulti returns separate per-statement results"
                             _ => putStrLn ("FAIL: execMulti returned wrong values: " ++ show multiResults)
       _ => putStrLn ("FAIL: execMulti returned wrong shape: " ++ show multiResults)

  -- withTransaction: a Left inside the action must roll back.
  Right _ <- execCommand db "CREATE TABLE tx_demo (id INT)" []
    | Left err => putStrLn ("FAIL create tx_demo: " ++ displayError err)
  _ <- withTransaction db {a = String} $ do
         _ <- execCommand db "INSERT INTO tx_demo (id) VALUES (1)" []
         pure (Left (ProtocolError "deliberate failure to force rollback"))
  Right afterRollback <- queryRows db "SELECT id FROM tx_demo" []
    | Left err => putStrLn ("FAIL select after rollback: " ++ displayError err)
  case afterRollback of
       [] => putStrLn "OK withTransaction rolled back on Left"
       _  => putStrLn ("FAIL: withTransaction did not roll back: " ++ show afterRollback)

  -- ...and commit on Right.
  _ <- withTransaction db (execCommand db "INSERT INTO tx_demo (id) VALUES (2)" [])
  Right afterCommit <- queryRows db "SELECT id FROM tx_demo" []
    | Left err => putStrLn ("FAIL select after commit: " ++ displayError err)
  case map (\r => getInt r "id") afterCommit of
       [Right 2] => putStrLn "OK withTransaction committed on Right"
       _         => putStrLn ("FAIL: withTransaction did not commit: " ++ show afterCommit)

  Just Idle <- txStatus db
    | other => putStrLn ("FAIL: expected Idle tx status after commit, got: " ++ show other)
  putStrLn "OK txStatus reports Idle after commit"

  _ <- execCommand db "DROP TABLE tx_demo" []

  -- Live checks for the fuller value typing (array/date/timestamp/numeric).
  Right _ <- execCommand db
    "CREATE TABLE types_demo (tags INT[], d DATE, ts TIMESTAMP, big NUMERIC)" []
    | Left err => putStrLn ("FAIL create types_demo: " ++ displayError err)
  Right _ <- execCommand db
    "INSERT INTO types_demo VALUES ($1, $2, $3, $4)"
    [ Just "{1,2,3}", Just "2024-03-07", Just "2024-03-07 13:45:30", Just "123456789012345678901234567890" ]
    | Left err => putStrLn ("FAIL insert types_demo: " ++ displayError err)
  Right [typesRow] <- queryRows db "SELECT tags, d, ts, big FROM types_demo" []
    | Left err => putStrLn ("FAIL select types_demo: " ++ displayError err)
    | Right rs => putStrLn ("FAIL: unexpected row count for types_demo: " ++ show rs)
  let tagsResult = getArray typesRow "tags"
  let dateResult = getDate typesRow "d"
  let tsResult = getTimestamp typesRow "ts"
  let bigResult = getInteger typesRow "big"
  let allOk = tagsResult == Right [Just "1", Just "2", Just "3"]
           && dateResult == Right (MkPGDate 2024 3 7)
           && tsResult == Right (MkPGTimestamp (MkPGDate 2024 3 7) 13 45 30)
           && bigResult == Right 123456789012345678901234567890
  if allOk
     then putStrLn "OK array/date/timestamp/numeric decode correctly"
     else putStrLn ("FAIL types_demo decode: " ++ show (tagsResult, dateResult, tsResult, bigResult))
  _ <- execCommand db "DROP TABLE types_demo" []

  -- Multi-dimensional array decoding, against Postgres's actual 2D output.
  Right [twoDRow] <- queryRows db "SELECT ARRAY[[1,2],[3,4]] AS m" []
    | Left err => putStrLn ("FAIL select 2D array: " ++ displayError err)
    | Right rs => putStrLn ("FAIL: unexpected row count for 2D array: " ++ show rs)
  case getArray2D twoDRow "m" of
       Right [[Just "1", Just "2"], [Just "3", Just "4"]] => putStrLn "OK 2D array decodes correctly"
       other => putStrLn ("FAIL 2D array decode: " ++ show other)

  -- JSONB decoding, against Postgres's actual output (which reformats/
  -- reorders/normalizes the literal, so this checks structure, not text).
  Right [jsonRow] <- queryRows db "SELECT '{\"a\":1,\"b\":[true,null,\"x\"]}'::jsonb AS j" []
    | Left err => putStrLn ("FAIL select jsonb: " ++ displayError err)
    | Right rs => putStrLn ("FAIL: unexpected row count for jsonb: " ++ show rs)
  case getJSON jsonRow "j" of
       Right (JObject [("a", JNumber 1.0), ("b", JArray [JBool True, JNull, JString "x"])]) =>
         putStrLn "OK JSONB decodes correctly"
       other => putStrLn ("FAIL JSONB decode: " ++ show other)

  -- cancelQuery: send a slow query on its own connection, then cancel it
  -- *before* reading the response - no client-side concurrency needed,
  -- since the cancellation races the server-side pg_sleep, not our client.
  Right dbSlow <- connectDB cfg
    | Left err => putStrLn ("FAIL connect for cancel test: " ++ displayError err)
  let slowFrame = encode (Parse "" "SELECT pg_sleep(2)" [])
                    ++ encode (Bind "" "" [])
                    ++ encode (Describe 'P' "")
                    ++ encode (Execute "" 0)
                    ++ encode Sync
  _ <- send (MkConnected (socket (conn dbSlow))) slowFrame
  cancelResult <- cancelQuery dbSlow
  case cancelResult of
       Left err => putStrLn ("FAIL cancelQuery: " ++ displayError err)
       Right () => do
         slowResponse <- handleQueryResponses dbSlow
         case slowResponse of
              Right [qr] => case errors qr of
                                 (e :: _) => putStrLn ("OK cancelQuery aborted the slow query: " ++ message e)
                                 []       => putStrLn "FAIL: slow query completed normally (not cancelled)"
              other => putStrLn ("FAIL: unexpected response to cancelled query: " ++ show other)
  closeDB dbSlow

  -- NOTIFY decoding: LISTEN on one connection, NOTIFY from another, and
  -- confirm the raw frame decodes correctly. No high-level API surfaces
  -- notifications yet (see Notification's doc comment), so this drives the
  -- low-level readFrame directly to check the decode fix itself.
  Right dbListener <- connectDB cfg
    | Left err => putStrLn ("FAIL connect listener: " ++ displayError err)
  Right _ <- execCommand dbListener "LISTEN idris2_pg_test_channel" []
    | Left err => putStrLn ("FAIL LISTEN: " ++ displayError err)
  Right dbNotifier <- connectDB cfg
    | Left err => putStrLn ("FAIL connect notifier: " ++ displayError err)
  Right _ <- execCommand dbNotifier "NOTIFY idris2_pg_test_channel, 'hello'" []
    | Left err => putStrLn ("FAIL NOTIFY: " ++ displayError err)
  closeDB dbNotifier
  notifyFrame <- readFrame (conn dbListener)
  case notifyFrame of
       Right (NotificationMsg (MkNotification _ "idris2_pg_test_channel" "hello")) =>
         putStrLn "OK NOTIFY decodes correctly"
       other => putStrLn ("FAIL: expected a matching NotificationMsg, got: " ++ show other)
  closeDB dbListener

  -- Regression test for the decodeInt32 sign-extension bug the unit tests
  -- caught (a NULL's -1 length marker was decoding as 4294967295, which
  -- would corrupt the rest of the row): a NULL bound as a parameter, and a
  -- NULL selected back, must both round-trip correctly alongside a real
  -- value in the same row.
  Right _ <- execCommand db "CREATE TABLE null_demo (a TEXT, b TEXT)" []
    | Left err => putStrLn ("FAIL create null_demo: " ++ displayError err)
  Right _ <- execCommand db "INSERT INTO null_demo (a, b) VALUES ($1, $2)" [Just "present", Nothing]
    | Left err => putStrLn ("FAIL insert null_demo: " ++ displayError err)
  Right [nullRow] <- queryRows db "SELECT a, b FROM null_demo" []
    | Left err => putStrLn ("FAIL select null_demo: " ++ displayError err)
    | Right rs => putStrLn ("FAIL: unexpected row count for null_demo: " ++ show rs)
  case (columnByName nullRow "a", columnByName nullRow "b") of
       (Just (Just "present"), Just Nothing) => putStrLn "OK NULL round-trips correctly alongside a real value"
       vals => putStrLn ("FAIL null_demo values: " ++ show vals)
  _ <- execCommand db "DROP TABLE null_demo" []

  -- Prepared statement caching: running the same query text twice should
  -- populate, then reuse, one cache entry keyed by that text (white-box
  -- check on DB.stmtCache, not just that results stay correct - that alone
  -- wouldn't prove caching actually happened rather than always
  -- re-Parse-ing). Other queries earlier in this test are cached too, so
  -- this looks up its own key rather than assuming an empty/singleton cache.
  let cacheQuery = "SELECT $1::int AS n"
  Right rows1 <- queryRows db cacheQuery [Just "5"]
    | Left err => putStrLn ("FAIL cache query 1: " ++ displayError err)
  cacheAfterFirst <- lookup cacheQuery <$> readIORef (stmtCache db)
  Right rows2 <- queryRows db cacheQuery [Just "7"]
    | Left err => putStrLn ("FAIL cache query 2: " ++ displayError err)
  cacheAfterSecond <- lookup cacheQuery <$> readIORef (stmtCache db)
  case (map (\r => getInt r "n") rows1, map (\r => getInt r "n") rows2) of
       ([Right 5], [Right 7]) =>
         case (cacheAfterFirst, cacheAfterSecond) of
              (Just name1, Just name2) =>
                if name1 == name2
                   then putStrLn "OK prepared statement cached and reused correctly"
                   else putStrLn ("FAIL: cache entry changed between calls: " ++ show (name1, name2))
              other => putStrLn ("FAIL: expected a cache entry both times: " ++ show other)
       other => putStrLn ("FAIL prepared statement caching results: " ++ show other)

  closeDB db
  putStrLn "OK done"
