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
  let cfg = mkPGConfig "127.0.0.1" 5432 "myuser" "mypassword" "mydb"
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

`Data.PGValue` decodes a `Row`'s columns on demand: `getText`, `getInt`,
`getInteger` (arbitrary precision), `getDouble`, `getBool`,
`getDate`/`getTimestamp` (`PGDate`/`PGTimestamp` records),
`getArray`/`getArray2D`/`getNestedArray` (Postgres arrays of any
dimensionality, via the `PGArrayValue` tree for anything beyond 2D), and
`getJSON` (`json`/`jsonb` columns, via a small dependency-free JSON parser
in `Data.PGJson` — no external JSON library needed).

`queryRows` returns text-format columns (the default). `queryRowsBinary`
requests binary format for every column instead; `getInt`/`getInteger`/
`getBool`/`getDouble`/`getText` understand both formats transparently
(binary floats are decoded via a from-scratch, verified-against-reference-values
IEEE754 implementation in `Data.PGBinary`, since Idris2 has no 32-bit-float
primitive to lean on). The other accessors (`getDate`/`getTimestamp`/
`getArray*`/`getJSON`) only support text format. Binary mode is opt-in and
less safe than text: unlike text parsing, a type mismatch (e.g. calling
`getDouble` on a binary `int4` column) isn't guaranteed to fail cleanly,
since binary formats don't self-describe their type the way text does.
Binary-format parameter *sending* isn't implemented — parameters are
always sent as text, which Postgres accepts and casts correctly for every
type.

### Timeouts

`PGConfig` has `connectTimeoutMs`/`readTimeoutMs : Maybe Nat` fields, both
`Nothing` (block indefinitely, the old behavior) by default via
`mkPGConfig`; set them with record update syntax, e.g.
`{ readTimeoutMs := Just 5000 } cfg`. `connectTimeoutMs` bounds `connectDB`
(the TCP connect plus the auth handshake) and `cancelQuery`'s own
out-of-band connection; `readTimeoutMs` bounds any single call that waits
on the server (`execCommand`/`queryRows`/`queryRowsBinary`/`execMulti`,
`waitForNotification`, `copyOut`/`copyIn`).

These are **not** OS-level socket timeouts (`SO_RCVTIMEO`/a non-blocking
`connect()`) — Idris2's `network` package has no support for those at all,
and adding it would mean shipping a hand-written C shared library that
every consumer of this package would need to compile before `pack build`
even works, which felt like too large a regression to how easy this
package is to install today. Instead, `Network.Timeout` races the
underlying call against a timer on a background thread (`fork` +
`Channel`, both already part of Idris2's base install — no new
dependency), and returns as soon as either finishes. That bounds how long
the *caller* waits, but not the underlying resource: if the timed-out call
was a blocking syscall stuck on a truly unresponsive server, timing out
here does not close the socket or interrupt that syscall — the abandoned
call keeps running in the background (its result, if any, is just never
read) until the OS's own TCP retry limit gives up, or the process exits.
This isn't always harmless: a timed-out `connectTimeoutMs` attempt against
an unreachable host was observed to interfere with an unrelated
connection attempted immediately afterward in the same process (in this
project's own test suite - see the ordering note in `test/src/Main.idr`),
likely by holding onto some OS-level resource for as long as it keeps
retrying. A connection whose read has timed out should be treated as
unusable and reconnected, not reused, and code with tight latency
requirements should be wary of firing off many timeout-bounded connection
attempts in a row.

### TLS

Set `PGConfig.useTLS = True` (via `MkPGConfig` or record update on a
`mkPGConfig`-built config) to require Postgres's SSLRequest negotiation and
a TLS 1.3 handshake before the startup message goes out; `connectDB` fails
outright if the server doesn't support SSL (there's no "prefer" fallback
to plaintext).

This is a from-scratch TLS 1.3 client (`Network.TLS`), the same philosophy
as everything else here: X25519 and P-256 ECDHE, ChaCha20-Poly1305, and
the RFC 8446 key schedule (HKDF-Extract/Expand-Label) are all hand-written
and verified against IETF/reference-library test vectors — see the
`Crypto.*`/`Network.TLS*` module comments for exactly which ones. Only
`TLS_CHACHA20_POLY1305_SHA256` is offered, and P-256 is what actually gets
negotiated in practice: Postgres's `ssl_ecdh_curve` setting defaults to
`prime256v1` and, on current Postgres/OpenSSL, can't be pointed at X25519
at all (a different OpenSSL key-machinery path) - offering only X25519
gets a `handshake failure` alert from a stock server, confirmed by testing
even bare `openssl s_client -groups x25519` against one. `Crypto.Curve25519`
is kept as a complete, independently-tested module even though the
handshake doesn't use it today.

**The one significant gap: no certificate signature verification.**
`CertificateVerify` is parsed and folded into the transcript hash (the
handshake can't complete without it), but its signature is never checked,
and `Certificate`'s contents are never inspected. That means the
connection is genuinely encrypted - safe from passive eavesdropping - but
the server's identity isn't authenticated, so an active
machine-in-the-middle presenting its own certificate wouldn't be detected.
Real X.509 parsing plus RSA/ECDSA signature verification is a large
enough sub-project (ASN.1 DER, a trust store) that it's a documented
follow-up rather than a blocker here. Everything else - the ECDHE key
exchange, the key schedule, and the record encryption - is exactly as
strong as a certificate-verifying client's.

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

Property-based tests ([idris2-hedgehog](https://github.com/stefan-hoeck/idris2-hedgehog),
no database needed): round-trip pairs (codecs, base64, AEAD encrypt/decrypt)
and algebraic invariants (X25519/P-256 Diffie-Hellman agreement symmetry)
generalized over random input, rather than the fixed examples/RFC vectors
the unit tests use. See `test/src/PropTests.idr` for what's covered and
what's deliberately out of scope.

```sh
cd test
pack build prop-test.ipkg
./build/exec/idris2-pg-prop-test
```

CRUD smoke test (needs a real Postgres — connection details come from
`PG_TEST_HOST`/`PG_TEST_PORT`/`PG_TEST_USER`/`PG_TEST_PASSWORD`/`PG_TEST_DB`,
defaulting to `127.0.0.1:5432`/`testuser`/`testpass`/`testdb`). A plain
default Postgres container already works, since SCRAM-SHA-256 (the
out-of-the-box default) is supported:

```sh
docker run -d --name idris2-pg-test \
  -e POSTGRES_USER=testuser -e POSTGRES_PASSWORD=testpass -e POSTGRES_DB=testdb \
  -p 5432:5432 postgres:16

cd test
pack build test.ipkg
./build/exec/idris2-pg-test
```

To exercise the MD5 path instead (also supported, but not the default since
Postgres 14), force `md5` password storage first:

```sh
docker run -d --name idris2-pg-test-md5 \
  -e POSTGRES_USER=testuser -e POSTGRES_PASSWORD=testpass -e POSTGRES_DB=testdb \
  -e POSTGRES_HOST_AUTH_METHOD=md5 -p 5432:5432 postgres:16

psql -h 127.0.0.1 -U testuser -d testdb -c "ALTER SYSTEM SET password_encryption = 'md5';"
psql -h 127.0.0.1 -U testuser -d testdb -c "SELECT pg_reload_conf();"
psql -h 127.0.0.1 -U testuser -d testdb -c "ALTER USER testuser WITH PASSWORD 'testpass';"
```

The smoke test's `testTLS` step exercises a real TLS 1.3 handshake if (and
only if) the server it connects to has SSL enabled - against a plain
`postgres:16` container (SSL off by default), it prints `SKIP TLS: server
does not have SSL enabled` rather than failing. To actually exercise it,
enable SSL on the container first (a self-signed cert generated and
installed at its default `ssl_ecdh_curve=prime256v1` - no special
configuration needed, since that's what this client negotiates by
default - see "TLS" above):

```sh
docker exec idris2-pg-test bash -c '
  cd "$(psql -U testuser -d testdb -tAc "show data_directory;")"
  openssl req -new -x509 -days 365 -nodes -out server.crt -keyout server.key -subj "/CN=localhost"
  chmod 600 server.key
  chown postgres:postgres server.key server.crt
'
psql -h 127.0.0.1 -U testuser -d testdb -c "ALTER SYSTEM SET ssl = on;"
docker restart idris2-pg-test
```

CI (`.github/workflows/ci.yml`) runs the unit tests, the property-based
tests, and both smoke test variants (SCRAM and MD5) on every push/PR; TLS
is not yet part of that
matrix (setting up SSL on a GitHub Actions service container needs
filesystem access this project hasn't wired into CI yet - see above for
running it manually) but is fully covered by the unit tests plus manual
live testing as described here.

## Features

- [x] Startup + MD5/cleartext/trust password authentication
- [x] Simple and extended (parameterized) query protocols
- [x] CREATE/SELECT/INSERT/UPDATE/DELETE/DROP, multi-statement batches (`execMulti`)
- [x] Transactions (`beginTx`/`commitTx`/`rollbackTx`/`withTransaction`, `txStatus`)
- [x] Query cancellation (`cancelQuery`)
- [x] NOTIFY payload decoding (see `Data.PGTypes.Notification`)
- [x] Value decoding: text/int/bool/double/arbitrary-precision integer/date/timestamp/array of any dimensionality/JSON (see "Value decoding" above)
- [x] Prepared statement caching — a query text is Parsed once per
      connection and reused on repeat calls (see `DB.stmtCache`).
- [x] Binary format for results (`queryRowsBinary`) — see "Value decoding"
      above for what's covered and its caveats. Sending binary-format
      parameters isn't implemented; parameters are always sent as text.
- [x] The `COPY` protocol (`copyOut`/`copyIn`) — bulk export/import via
      `COPY ... TO STDOUT`/`COPY ... FROM STDIN`, text format. `copyIn`
      sends the whole payload as a single CopyData message rather than
      chunking it.
- [x] SCRAM-SHA-256 auth — Postgres 14+'s default for new roles, built
      entirely from scratch (`Crypto.SHA256`, `Crypto.SCRAM`: HMAC-SHA256,
      PBKDF2, base64, the full RFC 5802 handshake including verifying the
      server's final signature). The client nonce comes from `contrib`'s
      `System.Random` (Chez's standard PRNG) - fine here since the nonce
      only needs to be unique, not secret, per RFC 5802. No channel binding
      (`SCRAM-SHA-256-PLUS`) yet - that would tie into the TLS handshake's
      exporter data, which is a natural follow-up now that TLS exists but
      hasn't been built.
- [x] LISTEN/NOTIFY (`listenChannel`/`unlistenChannel`/`waitForNotification`)
      — use a connection dedicated to listening, since `waitForNotification`
      blocks it until a notification arrives; it can't run other queries
      meanwhile; that wait can be bounded with `readTimeoutMs` (see
      "Timeouts" above).
- [x] Read/connect timeouts (`PGConfig.connectTimeoutMs`/`readTimeoutMs`) —
      cooperative, thread-based (`Network.Timeout`), not OS-level socket
      timeouts; see "Timeouts" above for exactly what that does and
      doesn't bound.
- [x] TLS 1.3 (`PGConfig.useTLS`) — the full handshake and record layer,
      built entirely from scratch: X25519 *and* P-256 ECDHE
      (`Crypto.Curve25519`/`Crypto.P256`), ChaCha20-Poly1305
      (`Crypto.ChaCha20`/`Crypto.Poly1305`/`Crypto.ChaCha20Poly1305`), the
      HKDF-based key schedule (`Crypto.HKDF`), and the handshake state
      machine (`Network.TLS`/`Network.TLSHandshake`/`Network.TLSWire`).
      See "TLS" above for what this does and doesn't protect against, and
      why P-256 (not X25519) is what's actually negotiated on the wire.
