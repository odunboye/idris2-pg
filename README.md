# idris2-pg

A PostgreSQL client for Idris2, implemented from scratch against the
[Postgres wire protocol](https://www.postgresql.org/docs/current/protocol.html)
over raw TCP sockets — no `libpq`, no FFI.

## Install / build

Requires [pack](https://github.com/stefan-hoeck/idris2-pack).

```sh
pack install idris2-pg
```

Or, from a checkout of this repo:

```sh
pack build idris2-pg.ipkg
```

## Usage

```idris
import Idris2_pg
import Data.PGTypes
import Data.PGValue

main : IO ()
main = do
  let cfg = MkPGConfig "127.0.0.1" 5432 "myuser" "mypassword" "mydb"
  Right db <- connectDB cfg
    | Left err => putStrLn (displayError err)

  -- INSERT/UPDATE/DELETE/DDL - parameters are sent via the extended query
  -- protocol, never string-interpolated into the SQL.
  Right _ <- execCommand db
    "INSERT INTO users (name, email) VALUES ($1, $2)"
    [Just "Ada", Just "ada@example.com"]
    | Left err => putStrLn (displayError err)

  -- SELECT
  Right rows <- queryRows db "SELECT name, email FROM users" []
    | Left err => putStrLn (displayError err)
  traverse_ (\row => case (getText row "name", getText row "email") of
                           (Right name, Right email) => putStrLn (name ++ " <" ++ email ++ ">")
                           _ => pure ())
            rows

  -- Transactions
  _ <- withTransaction db $ do
         _ <- execCommand db "UPDATE accounts SET balance = balance - 100 WHERE id = $1" [Just "1"]
         execCommand db "UPDATE accounts SET balance = balance + 100 WHERE id = $1" [Just "2"]

  closeDB db
```

See `test/src/Main.idr` for a fuller worked example (CRUD, transactions,
`execMulti`, `cancelQuery`, array/date/timestamp/numeric values, NULL
handling).

### Value decoding

`Data.PGValue` decodes a `Row`'s text-format columns on demand:
`getText`, `getInt`, `getInteger` (arbitrary precision), `getDouble`,
`getBool`, `getDate`/`getTimestamp` (`PGDate`/`PGTimestamp` records), and
`getArray` (one-dimensional Postgres arrays, e.g. `int[]`/`text[]`). JSON and
JSONB columns come back as plain text via `getText` — bring your own JSON
library (e.g. the `json` package) to decode further if you need to.

### Errors

Every fallible call returns `Either PGError a`, where `PGError` is one of
`ConnectionError` (transport-level), `ProtocolError` (an unexpected/malformed
response), or `SqlError Error` (a genuine error from the server — inspect it
with `message`, `detail`, `hint`, `schemaName`, `tableName`, `columnName`,
`constraintName`, etc.). `displayError` renders any of them as a message.

## Running the tests

Unit tests (codec + value parsers, no database needed):

```sh
cd test
pack build unit-test.ipkg
./build/exec/idris2-pg-unit-test
```

CRUD smoke test (needs a real Postgres — connection details come from
`PG_TEST_HOST`/`PG_TEST_PORT`/`PG_TEST_USER`/`PG_TEST_PASSWORD`/`PG_TEST_DB`,
defaulting to `127.0.0.1:5432`/`testuser`/`testpass`/`testdb`):

```sh
docker run -d --name idris2-pg-test \
  -e POSTGRES_USER=testuser -e POSTGRES_PASSWORD=testpass -e POSTGRES_DB=testdb \
  -e POSTGRES_HOST_AUTH_METHOD=md5 -p 5432:5432 postgres:16

# Postgres 14+ defaults to scram-sha-256 password storage even when
# pg_hba.conf says "md5" - force real MD5 auth to match what this client
# supports:
psql -h 127.0.0.1 -U testuser -d testdb -c "ALTER SYSTEM SET password_encryption = 'md5';"
psql -h 127.0.0.1 -U testuser -d testdb -c "SELECT pg_reload_conf();"
psql -h 127.0.0.1 -U testuser -d testdb -c "ALTER USER testuser WITH PASSWORD 'testpass';"

cd test
pack build test.ipkg
./build/exec/idris2-pg-test
```

CI (`.github/workflows/ci.yml`) runs both on every push/PR.

## Supported

- Startup + MD5/cleartext/trust password authentication
- Simple and extended (parameterized) query protocols
- CREATE/SELECT/INSERT/UPDATE/DELETE/DROP, multi-statement batches
  (`execMulti`), transactions (`beginTx`/`commitTx`/`rollbackTx`/
  `withTransaction`, `txStatus`)
- Query cancellation (`cancelQuery`)
- NOTIFY payload decoding (see below)
- Text/int/bool/double/arbitrary-precision-integer/date/timestamp/
  one-dimensional-array value decoding

## Not supported

- **SCRAM-SHA-256 auth** — Postgres 14+'s default for new roles. Only
  trust/md5/cleartext are implemented; a role authenticating against this
  client needs `password_encryption = md5` (see above) or `trust`.
- **TLS/SSL** — the underlying socket layer has no TLS support at all.
- **The `COPY` protocol** — no bulk import/export.
- **Binary format** — everything is text format, both for parameters sent
  and results received.
- **Read/connect timeouts** — a hung or unresponsive server can block a call
  indefinitely; there's no way to bound that today.
- **LISTEN/NOTIFY consumption** — `NotificationResponse` decodes correctly
  (see `Data.PGTypes.Notification`), but nothing exposes a way to `LISTEN`
  and then wait for/consume notifications without blocking on an unrelated
  query's response; that needs the read-timeout work above to do well.
- **Prepared statement caching** — every parameterized call uses a fresh
  unnamed statement/portal; nothing is cached or reused across calls.
- **Multi-dimensional arrays, JSON/JSONB typed decoding** — arrays are
  one-dimensional scalars only; JSON/JSONB come back as raw text (see
  Value decoding above).
