module Network.TLS

-- The TLS 1.3 client handshake and record layer, tying together
-- Crypto.P256/ChaCha20Poly1305/HKDF and Network.TLSWire/
-- TLSHandshake into an actual connection over a real Socket.
--
-- Scope, deliberately: TLS_CHACHA20_POLY1305_SHA256 only, P-256 only,
-- no session resumption/0-RTT, and - the biggest omission - no
-- certificate signature verification. CertificateVerify is parsed and
-- folded into the transcript hash (required for the handshake to
-- complete at all) but its signature is never checked, and the
-- Certificate message's contents are never inspected. That means this
-- protects the connection against passive eavesdropping (the wire is
-- genuinely encrypted) but not an active machine-in-the-middle
-- presenting its own certificate - the server's identity is never
-- authenticated. Real X.509/RSA-or-ECDSA signature verification is a
-- large enough sub-project (ASN.1 DER parsing, a trust store) that it's
-- being left as a documented follow-up rather than a blocker (see
-- README). Everything else here - the ECDHE key exchange, the key
-- schedule, and the record encryption itself - is exactly as strong as
-- what a certificate-verifying client would use, since none of it
-- depends on trusting the certificate.
--
-- Verified live against a stock, unmodified `postgres:16` container with
-- ssl=on (default ssl_ecdh_curve=prime256v1 - see Network.TLSHandshake's
-- module comment for why P-256, not X25519): full handshake, SCRAM-SHA-256
-- authentication carried over it, a real query, and a clean Terminate.

import Network.Socket
import Network.RawSocket
import Network.Core
import Network.TLSWire
import Network.TLSHandshake
import Crypto.P256
import Crypto.ChaCha20Poly1305
import Crypto.HKDF
import Crypto.SHA256
import Data.IORef
import Data.Bits
import Data.List

-- RFC 8446 section 5.3: the record nonce is the write IV XOR the
-- 8-byte big-endian sequence number, left-padded with zeros to the IV's
-- length (12 bytes for the 96-bit nonces every AEAD registered for TLS
-- 1.3 uses).
beBytesN : Nat -> Nat -> List Bits8
beBytesN Z     _ = []
beBytesN (S k) n = beBytesN k (n `div` 256) ++ [cast (n `mod` 256)]

nonceFor : (iv : List Bits8) -> (seqNum : Nat) -> List Bits8
nonceFor iv seqNum = zipWith xor iv (beBytesN 12 seqNum)

sendPlaintextRecord : Socket -> (contentType : Bits8) -> (fragment : List Bits8) -> IO (Either String ())
sendPlaintextRecord sock contentType fragment =
  -- 0x0301 for the initial ClientHello record is the common-practice,
  -- middlebox-friendly choice (RFC 8446 section 5.1, also what RFC 8448's
  -- own trace uses); TLS 1.3 receivers ignore this field regardless.
  let recordVersion : List Bits8
      recordVersion = if contentType == 22 then [0x03, 0x01] else [0x03, 0x03]
      header        = [contentType] ++ recordVersion ++ u16 (length fragment)
  in send (MkConnected sock) (header ++ fragment)

readRecord : Socket -> IO (Either String (Bits8, List Bits8))
readRecord sock = do
  Right hdr <- receiveExact (MkConnected sock) 5
    | Left err => pure (Left err)
  case hdr of
       [ct, verHi, verLo, lenHi, lenLo] => do
         let len : Nat
             len = cast lenHi * 256 + cast lenLo
         Right fragment <- receiveExact (MkConnected sock) (cast len)
           | Left err => pure (Left err)
         pure (Right (ct, fragment))
       _ => pure (Left "TLS: short record header")

-- RFC 8446 section 5.4: TLSInnerPlaintext is `content || real_type ||
-- zeros*` - strip the (possibly absent) zero padding, then the last
-- remaining byte is the real content type.
unpadInner : List Bits8 -> Maybe (Bits8, List Bits8)
unpadInner bytes =
  case reverse (dropWhile (== 0) (reverse bytes)) of
       []           => Nothing
       nonZeroTrail => case reverse nonZeroTrail of
                            (ct :: revContent) => Just (ct, reverse revContent)
                            []                 => Nothing

writeEncryptedRecord : Socket -> (key : List Bits8) -> (iv : List Bits8) -> IORef Nat
                     -> (realContentType : Bits8) -> (content : List Bits8) -> IO (Either String ())
writeEncryptedRecord sock key iv seqRef realContentType content = do
  seqNum <- readIORef seqRef
  let nonce      = nonceFor iv seqNum
      inner      = content ++ [realContentType]
      cipherLen  = length inner + 16 -- Poly1305 tag
      header     = [23, 0x03, 0x03] ++ u16 cipherLen
      (ct, tag)  = encrypt key nonce header inner
  writeIORef seqRef (seqNum + 1)
  send (MkConnected sock) (header ++ ct ++ tag)

readEncryptedRecord : Socket -> (key : List Bits8) -> (iv : List Bits8) -> IORef Nat
                    -> IO (Either String (Bits8, List Bits8))
readEncryptedRecord sock key iv seqRef = do
  Right (outerCt, fragment) <- readRecord sock
    | Left err => pure (Left err)
  -- RFC 8446 section 5: a compliant TLS 1.3 endpoint may send a
  -- middlebox-compatibility ChangeCipherSpec record (content type 20,
  -- always the single byte 0x01) right after ServerHello. It's never
  -- encrypted and never counts toward the record sequence number - just
  -- discard it and read the next record instead.
  if outerCt == 20
     then readEncryptedRecord sock key iv seqRef
     else do
       seqNum <- readIORef seqRef
       let len = length fragment
       if len < 16
          then pure (Left "TLS: encrypted record shorter than an auth tag")
          else do
            let (ciphertext, tag) = splitAt (len `minus` 16) fragment
                nonce             = nonceFor iv seqNum
                header            = [outerCt, 0x03, 0x03] ++ u16 len
            case decrypt key nonce header ciphertext tag of
                 Nothing => pure (Left "TLS: record authentication failed")
                 Just inner => do
                   writeIORef seqRef (seqNum + 1)
                   case unpadInner inner of
                        Nothing              => pure (Left "TLS: empty inner plaintext")
                        Just (realCt, plain) => pure (Right (realCt, plain))

-- Repeatedly decrypts handshake-type records into `bufRef` until it holds
-- at least one complete handshake message, then pulls that message off.
-- Handles both a message split across records and several messages
-- coalesced into one record.
readNextHandshakeMessage : Socket -> (key : List Bits8) -> (iv : List Bits8) -> IORef Nat
                         -> IORef (List Bits8) -> IO (Either String (Nat, List Bits8))
readNextHandshakeMessage sock key iv seqRef bufRef = do
  buf <- readIORef bufRef
  case decodeHandshakeMessage buf of
       Just (ty, body, rest) => do
         writeIORef bufRef rest
         pure (Right (ty, body))
       Nothing => do
         Right (ct, content) <- readEncryptedRecord sock key iv seqRef
           | Left err => pure (Left err)
         if ct == 22
            then do
              writeIORef bufRef (buf ++ content)
              readNextHandshakeMessage sock key iv seqRef bufRef
            else if ct == 21
                    then pure (Left ("TLS: received an alert during the handshake: " ++ show content))
                    else readNextHandshakeMessage sock key iv seqRef bufRef

public export
record TLSSession where
  constructor MkTLSSession
  tlsSocket   : Socket
  writeKey    : List Bits8
  writeIV     : List Bits8
  writeSeqRef : IORef Nat
  readKey     : List Bits8
  readIV      : List Bits8
  readSeqRef  : IORef Nat
  recvBufRef  : IORef (List Bits8)

hkdfKeyIV : (secret : List Bits8) -> (List Bits8, List Bits8)
hkdfKeyIV secret = (hkdfExpandLabel secret "key" [] 32, hkdfExpandLabel secret "iv" [] 12)

||| Performs the full TLS 1.3 client handshake over an already-connected
||| raw TCP `Socket`, returning a TLSSession for ongoing encrypted
||| application traffic. See the module comment for exactly what is and
||| isn't verified.
export
tlsClientHandshake : Socket -> IO (Either String TLSSession)
tlsClientHandshake sock = do
  Right clientRandom <- randomBytes 32
    | Left err => pure (Left err)
  Right clientPrivKey <- randomBytes 32
    | Left err => pure (Left err)
  let clientPubKey = p256PublicKey clientPrivKey
      clientHello  = buildClientHello clientRandom clientPubKey
  Right () <- sendPlaintextRecord sock 22 clientHello
    | Left err => pure (Left err)
  Right (shOuterCt, shFragment) <- readRecord sock
    | Left err => pure (Left err)
  if shOuterCt /= 22
     then pure (Left "TLS: expected a handshake record for ServerHello")
     else case decodeHandshakeMessage shFragment of
       Nothing => pure (Left "TLS: malformed ServerHello record")
       Just (shTy, shBody, extra) =>
         if shTy /= htServerHello
            then pure (Left "TLS: expected a ServerHello message")
            else case parseServerHello shBody of
              Nothing => pure (Left "TLS: could not parse ServerHello (no P-256 key_share?)")
              Just sh => do
                let serverHelloBytes = take (length shFragment `minus` length extra) shFragment
                let Just sharedSecret = p256SharedSecret clientPrivKey (serverPublicKey sh)
                    | Nothing => pure (Left "TLS: invalid server P-256 public key")
                let transcriptCHSH   = clientHello ++ serverHelloBytes
                    hashEmpty        = sha256 []
                    earlySecret      = hkdfExtract (replicate 32 0) (replicate 32 0)
                    derivedForHS     = deriveSecret earlySecret "derived" hashEmpty
                    handshakeSecret  = hkdfExtract derivedForHS sharedSecret
                    hashCHSH         = sha256 transcriptCHSH
                    clientHSTraffic  = deriveSecret handshakeSecret "c hs traffic" hashCHSH
                    serverHSTraffic  = deriveSecret handshakeSecret "s hs traffic" hashCHSH
                    (clientHSKey, clientHSIV) = hkdfKeyIV clientHSTraffic
                    (serverHSKey, serverHSIV) = hkdfKeyIV serverHSTraffic
                serverSeqRef <- newIORef 0
                bufRef       <- newIORef (the (List Bits8) [])
                Right (eeTy, eeBody) <- readNextHandshakeMessage sock serverHSKey serverHSIV serverSeqRef bufRef
                  | Left err => pure (Left err)
                if eeTy /= htEncryptedExtensions
                   then pure (Left "TLS: expected EncryptedExtensions")
                   else do
                     Right (certTy, certBody) <- readNextHandshakeMessage sock serverHSKey serverHSIV serverSeqRef bufRef
                       | Left err => pure (Left err)
                     if certTy /= htCertificate
                        then pure (Left "TLS: expected Certificate")
                        else do
                          Right (cvTy, cvBody) <- readNextHandshakeMessage sock serverHSKey serverHSIV serverSeqRef bufRef
                            | Left err => pure (Left err)
                          if cvTy /= htCertificateVerify
                             then pure (Left "TLS: expected CertificateVerify")
                             else do
                               Right (finTy, finBody) <- readNextHandshakeMessage sock serverHSKey serverHSIV serverSeqRef bufRef
                                 | Left err => pure (Left err)
                               if finTy /= htFinished
                                  then pure (Left "TLS: expected server Finished")
                                  else do
                                    let eeBytes   = handshakeMessage htEncryptedExtensions eeBody
                                        certBytes = handshakeMessage htCertificate certBody
                                        cvBytes   = handshakeMessage htCertificateVerify cvBody
                                        transcriptBeforeFinished = transcriptCHSH ++ eeBytes ++ certBytes ++ cvBytes
                                        hashBeforeFinished       = sha256 transcriptBeforeFinished
                                        expectedServerFinished   = computeFinished serverHSTraffic hashBeforeFinished
                                    if expectedServerFinished /= finBody
                                       then pure (Left "TLS: server Finished verification failed")
                                       else do
                                         let finishedBytes         = handshakeMessage htFinished finBody
                                             transcriptWithSFin    = transcriptBeforeFinished ++ finishedBytes
                                             hashWithServerFinished = sha256 transcriptWithSFin
                                             derivedForMaster      = deriveSecret handshakeSecret "derived" hashEmpty
                                             masterSecret          = hkdfExtract derivedForMaster (replicate 32 0)
                                             myFinishedBody        = computeFinished clientHSTraffic hashWithServerFinished
                                             myFinishedBytes       = handshakeMessage htFinished myFinishedBody
                                         clientSeqRef <- newIORef 0
                                         Right () <- writeEncryptedRecord sock clientHSKey clientHSIV clientSeqRef 22 myFinishedBytes
                                           | Left err => pure (Left err)
                                         -- RFC 8446 section 7.1: both application traffic secrets are
                                         -- derived from the transcript hash "ClientHello...server
                                         -- Finished" - up to and including the SERVER's Finished only.
                                         -- The client's own Finished is never part of this hash (it's
                                         -- also why the server can derive and start using its half of
                                         -- these keys before ever seeing the client's Finished).
                                         let clientAppTraffic = deriveSecret masterSecret "c ap traffic" hashWithServerFinished
                                             serverAppTraffic = deriveSecret masterSecret "s ap traffic" hashWithServerFinished
                                             (clientAppKey, clientAppIV) = hkdfKeyIV clientAppTraffic
                                             (serverAppKey, serverAppIV) = hkdfKeyIV serverAppTraffic
                                         appWriteSeqRef <- newIORef 0
                                         appReadSeqRef  <- newIORef 0
                                         recvBufRef     <- newIORef (the (List Bits8) [])
                                         pure (Right (MkTLSSession sock clientAppKey clientAppIV appWriteSeqRef
                                                                    serverAppKey serverAppIV appReadSeqRef recvBufRef))

||| Sends `bytes` as one TLS application_data record.
export
tlsSend : TLSSession -> List Bits8 -> IO (Either String ())
tlsSend session bytes =
  writeEncryptedRecord (tlsSocket session) (writeKey session) (writeIV session) (writeSeqRef session) 23 bytes

||| Reads exactly `n` bytes of decrypted application data, decrypting
||| further records as needed and buffering any leftover. A stray
||| handshake-type record (e.g. a post-handshake NewSessionTicket) is
||| silently skipped; an alert is fatal.
export
tlsReceiveExact : TLSSession -> Int -> IO (Either String (List Bits8))
tlsReceiveExact session n = go
  where
    go : IO (Either String (List Bits8))
    go = do
      buf <- readIORef (recvBufRef session)
      if length buf >= cast n
         then do
           let (want, rest) = splitAt (cast n) buf
           writeIORef (recvBufRef session) rest
           pure (Right want)
         else do
           Right (ct, content) <- readEncryptedRecord (tlsSocket session) (readKey session) (readIV session) (readSeqRef session)
             | Left err => pure (Left err)
           if ct == 23
              then do
                writeIORef (recvBufRef session) (buf ++ content)
                go
              else if ct == 21
                      then pure (Left ("TLS: received an alert: " ++ show content))
                      else go
