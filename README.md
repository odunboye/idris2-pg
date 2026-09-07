# idris2-pg

A PostgreSQL client for Idris2, implemented from scratch against the
[Postgres wire protocol](https://www.postgresql.org/docs/current/protocol.html)
over raw TCP sockets — no `libpq`, no FFI.

## Project goals

The main goal of this project is a **fully verified** Postgres client: one
where Idris2's dependent types are used to *prove* protocol-level
correctness properties at compile time, not just exercise them with tests —
an encode/decode pair proven to round-trip, a connection state machine the
compiler actually enforces rather than only labels, length-indexed buffers
that turn a short read or a frame overrun into a type error instead of a
runtime one, and so on. That work happens on the
[`verified`](https://github.com/odunboye/idris2-pg/tree/verified) branch,
and is meant as a demonstration of what dependent types buy you in a real,
non-toy client for a real wire protocol, not a toy example.

This `main` branch is the practical first step toward that goal: a
**usable**, thoroughly tested (unit tests plus a live end-to-end CRUD suite —
see "Running the tests" below) client, built first to have a working,
protocol-correct reference implementation before attempting to formally
prove anything about it. Everything documented below describes this branch;
it remains useful in its own right — including as the reference the
`verified` branch's proofs get checked against — independent of how far that
work progresses.

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

## Features

- [x] Startup + MD5/cleartext/trust password authentication
- [x] Simple and extended (parameterized) query protocols
- [x] CREATE/SELECT/INSERT/UPDATE/DELETE/DROP, multi-statement batches (`execMulti`)
- [x] Transactions (`beginTx`/`commitTx`/`rollbackTx`/`withTransaction`, `txStatus`)
- [x] Query cancellation (`cancelQuery`)
- [x] NOTIFY payload decoding (see `Data.PGTypes.Notification`)
- [x] Value decoding: text/int/bool/double/arbitrary-precision integer/date/timestamp/one-dimensional array (see "Value decoding" above)
- [ ] SCRAM-SHA-256 auth — Postgres 14+'s default for new roles. Only
      trust/md5/cleartext are implemented; a role authenticating against this
      client needs `password_encryption = md5` (see above) or `trust`.
- [ ] TLS/SSL — the underlying socket layer has no TLS support at all.
- [ ] The `COPY` protocol — no bulk import/export.
- [ ] Binary format — everything is text format, both for parameters sent
      and results received.
- [ ] Read/connect timeouts — a hung or unresponsive server can block a call
      indefinitely; there's no way to bound that today.
- [ ] LISTEN/NOTIFY consumption — decoding works, but nothing exposes a way
      to `LISTEN` and then wait for/consume notifications without blocking
      on an unrelated query's response; that needs the read-timeout work
      above to do well.
- [ ] Prepared statement caching — every parameterized call uses a fresh
      unnamed statement/portal; nothing is cached or reused across calls.
- [ ] Multi-dimensional arrays, JSON/JSONB typed decoding — arrays are
      one-dimensional scalars only; JSON/JSONB come back as raw text (see
      "Value decoding" above).
