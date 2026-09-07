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
    | Left err => putStrLn ("FAIL connect: " ++ err)
  putStrLn "OK connected"

  _ <- execCommand db "DROP TABLE IF EXISTS crud_demo" []

  Right _ <- execCommand db "CREATE TABLE crud_demo (id INT PRIMARY KEY, name TEXT)" []
    | Left err => putStrLn ("FAIL create table: " ++ err)
  putStrLn "OK create table"

  Right tag1 <- execCommand db "INSERT INTO crud_demo (id, name) VALUES ($1, $2)" [Just "1", Just "Alice"]
    | Left err => putStrLn ("FAIL insert: " ++ err)
  putStrLn ("OK insert: " ++ tag1)

  Right _ <- execCommand db "INSERT INTO crud_demo (id, name) VALUES ($1, $2)" [Just "2", Just "Bob"]
    | Left err => putStrLn ("FAIL insert 2: " ++ err)

  Right rows <- queryRows db "SELECT id, name FROM crud_demo ORDER BY id" []
    | Left err => putStrLn ("FAIL select: " ++ err)
  putStrLn ("OK select: " ++ show rows)

  Right tag3 <- execCommand db "UPDATE crud_demo SET name = $1 WHERE id = $2" [Just "Alicia", Just "1"]
    | Left err => putStrLn ("FAIL update: " ++ err)
  putStrLn ("OK update: " ++ tag3)

  Right tag4 <- execCommand db "DELETE FROM crud_demo WHERE id = $1" [Just "2"]
    | Left err => putStrLn ("FAIL delete: " ++ err)
  putStrLn ("OK delete: " ++ tag4)

  -- Regression test for the Phase 1 ErrorResponse decode fix: a malformed
  -- query must surface as a Left, not crash the process.
  badResult <- queryRows db "SELECT nonexistent_column FROM crud_demo" []
  case badResult of
       Left err => putStrLn ("OK graceful error on bad query: " ++ err)
       Right _  => putStrLn "FAIL: malformed query did not report an error"

  -- Regression test for the Phase 0 short-read fix: round-trip a value large
  -- enough that the server's response can't arrive in a single TCP read.
  let bigString = pack (replicate 100000 'x')
  Right _ <- execCommand db "CREATE TABLE big_demo (val TEXT)" []
    | Left err => putStrLn ("FAIL create big table: " ++ err)
  Right _ <- execCommand db "INSERT INTO big_demo (val) VALUES ($1)" [Just bigString]
    | Left err => putStrLn ("FAIL insert big value: " ++ err)
  Right bigRows <- queryRows db "SELECT val FROM big_demo" []
    | Left err => putStrLn ("FAIL select big value: " ++ err)
  case bigRows of
       [row] => case getText row "val" of
                     Right v => putStrLn ("OK large value round-trip, length matches: " ++ show (length v == 100000))
                     Left err => putStrLn ("FAIL decode big value: " ++ err)
       _ => putStrLn "FAIL: unexpected row count for big_demo"
  _ <- execCommand db "DROP TABLE big_demo" []

  Right _ <- execCommand db "DROP TABLE crud_demo" []
    | Left err => putStrLn ("FAIL final drop: " ++ err)

  closeDB db
  putStrLn "OK done"
