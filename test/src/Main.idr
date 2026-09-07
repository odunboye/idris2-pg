module Main

import Data.Maybe
import Data.String
import System
import Idris2_pg
import Data.PGTypes
import Data.PGValue

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

  closeDB db
  putStrLn "OK done"
