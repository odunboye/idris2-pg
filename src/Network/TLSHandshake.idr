module Network.TLSHandshake

-- Pure construction/parsing of the TLS 1.3 handshake messages this client
-- needs (RFC 8446 section 4): ClientHello, ServerHello, and just enough
-- of EncryptedExtensions/Certificate/CertificateVerify to skip over them
-- (no certificate verification in this first landing - see README/
-- Network.TLS's module comment for that scope decision), plus Finished.
--
-- Key exchange group: secp256r1 (P-256), not x25519. Postgres's
-- ssl_ecdh_curve GUC defaults to "prime256v1" and - discovered empirically
-- while building this - can't be pointed at x25519 at all on current
-- Postgres/OpenSSL (it only accepts a classic named EC_KEY curve; x25519
-- is a different OpenSSL key type). Offering only x25519 gets a
-- "handshake failure" alert from a stock `postgres:16` container, and
-- even bare `openssl s_client -groups x25519` gets the same failure
-- against it - confirmed to be the server's default configuration, not a
-- bug in this client, before switching the offered group.

import Network.TLSWire
import Crypto.P256
import Crypto.HKDF
import Crypto.SCRAM
import System.File
import Data.Buffer
import Data.List
import Data.Bits

-- Cipher suite: TLS_CHACHA20_POLY1305_SHA256 (RFC 8446 Appendix B.4).
public export
cipherSuiteChaCha20Poly1305 : Nat
cipherSuiteChaCha20Poly1305 = 0x1303

bufferBytes : Buffer -> (offset : Nat) -> (len : Nat) -> IO (List Bits8)
bufferBytes buf offset Z = pure []
bufferBytes buf offset (S k) = do
  b    <- getBits8 buf (cast offset)
  rest <- bufferBytes buf (S offset) k
  pure (b :: rest)

||| Cryptographically-secure random bytes, read directly from the OS's
||| CSPRNG (/dev/urandom) rather than a userspace PRNG. contrib's
||| System.Random resolves to Chez's plain, non-cryptographic `random`
||| (JS: Math.random()) - fine for the SCRAM client nonce (see
||| Crypto.SCRAM's module comment, where predictability doesn't matter)
||| but not for the ECDHE private key generated below, where it would
||| make the key recoverable.
export
randomBytes : Nat -> IO (Either String (List Bits8))
randomBytes n = do
  Right fh <- openFile "/dev/urandom" Read
    | Left err => pure (Left ("TLS: could not open /dev/urandom: " ++ show err))
  Just buf <- newBuffer (cast n)
    | Nothing => do
        closeFile fh
        pure (Left "TLS: could not allocate random buffer")
  result <- readAll fh buf 0
  closeFile fh
  pure result
  where
    readAll : File -> Buffer -> (got : Int) -> IO (Either String (List Bits8))
    readAll fh buf got =
      if got >= cast n
         then Right <$> bufferBytes buf 0 n
         else do
           Right r <- readBufferData fh buf got (cast n - got)
             | Left err => pure (Left "TLS: could not read /dev/urandom")
           if r <= 0
              then pure (Left "TLS: /dev/urandom read returned no data")
              else readAll fh buf (got + r)

extSupportedVersionsBody : Bytes
extSupportedVersionsBody = [u8 2] ++ u16 0x0304  -- just TLS 1.3

extSupportedGroupsBody : Bytes
extSupportedGroupsBody = u16 2 ++ u16 groupSecp256r1

-- A minimal, standard set - ecdsa_secp256r1_sha256, rsa_pss_rsae_sha256,
-- rsa_pkcs1_sha256, ed25519 - enough for any common server certificate.
-- Not used to verify anything yet (no signature verification), but RFC
-- 8446 section 4.2.3 requires clients to send this extension regardless.
extSignatureAlgorithmsBody : Bytes
extSignatureAlgorithmsBody =
  let schemes = concatMap u16 [0x0403, 0x0804, 0x0401, 0x0807]
  in u16 (length schemes) ++ schemes

extKeyShareBody : (clientPublicKey : Bytes) -> Bytes
extKeyShareBody pubKey =
  let entry = u16 groupSecp256r1 ++ encodeVec16 pubKey
  in encodeVec16 entry

||| Builds a ClientHello handshake message (including the 1-byte type +
||| 3-byte length header) offering only TLS_CHACHA20_POLY1305_SHA256 and
||| a P-256 key share (`clientPublicKey`: the 65-byte SEC1 uncompressed
||| point from Crypto.P256.p256PublicKey).
export
buildClientHello : (clientRandom : Bytes) -> (clientPublicKey : Bytes) -> Bytes
buildClientHello clientRandom clientPublicKey =
  let legacyVersion    = u16 0x0303
      sessionId         = encodeVec8 []  -- empty; no middlebox-compat padding needed for a direct connection
      cipherSuites      = encodeVec16 (u16 cipherSuiteChaCha20Poly1305)
      compressionMethods = encodeVec8 [0]
      extensions        = encodeVec16 $
                             encodeExtension extSupportedVersions extSupportedVersionsBody
                          ++ encodeExtension extSupportedGroups extSupportedGroupsBody
                          ++ encodeExtension extSignatureAlgorithms extSignatureAlgorithmsBody
                          ++ encodeExtension extKeyShare (extKeyShareBody clientPublicKey)
      body = legacyVersion ++ clientRandom ++ sessionId ++ cipherSuites
               ++ compressionMethods ++ extensions
  in handshakeMessage htClientHello body

uncons1 : Bytes -> Maybe (Bits8, Bytes)
uncons1 (b :: rest) = Just (b, rest)
uncons1 []          = Nothing

public export
record ParsedServerHello where
  constructor MkParsedServerHello
  serverRandom    : Bytes
  cipherSuite     : Nat
  serverPublicKey : Bytes

||| Parses a ServerHello message BODY (not including the handshake header -
||| the caller strips that via decodeHandshakeMessage first). Fails if the
||| server didn't offer a P-256 key_share, or the message is malformed.
export
parseServerHello : Bytes -> Maybe ParsedServerHello
parseServerHello body = do
  (legacyVersion, r1)     <- decodeU16 body
  let (serverRandom, r2)  = splitAt 32 r1
  (sessionIdEcho, r3)     <- decodeVec8 r2
  (cipherSuite, r4)       <- decodeU16 r3
  (compressionMethod, r5) <- uncons1 r4
  (extBytes, afterExts)   <- decodeVec16 r5
  exts                    <- decodeExtensions extBytes
  keyShareBody            <- findExtension extKeyShare exts
  (group, ks1)            <- decodeU16 keyShareBody
  (serverPublicKey, ks2)  <- decodeVec16 ks1
  if group == groupSecp256r1 && length serverPublicKey == 65 && length serverRandom == 32
     then Just (MkParsedServerHello serverRandom cipherSuite serverPublicKey)
     else Nothing

||| RFC 8446 section 4.4.4's finished_key and the HMAC verify_data over a
||| transcript hash - shared by both computing our own Finished (keyed on
||| our own handshake traffic secret) and verifying the server's (keyed on
||| theirs).
export
computeFinished : (trafficSecret : Bytes) -> (transcriptHash : Bytes) -> Bytes
computeFinished trafficSecret transcriptHash =
  let finishedKey = hkdfExpandLabel trafficSecret "finished" [] 32
  in hmacSha256 finishedKey transcriptHash

||| Builds a Finished handshake message (header + verify_data).
export
buildFinished : (trafficSecret : Bytes) -> (transcriptHash : Bytes) -> Bytes
buildFinished trafficSecret transcriptHash =
  handshakeMessage htFinished (computeFinished trafficSecret transcriptHash)
