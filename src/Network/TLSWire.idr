module Network.TLSWire

-- Wire encoding/decoding for TLS 1.3 handshake messages (RFC 8446 section
-- 4) - pure functions, no sockets, so this is unit-testable on its own.
-- Deliberately independent of Helper.idr's PG-specific int codecs (those
-- are signed and PG-flavored; TLS's length fields are unsigned 1/2/3-byte
-- big-endian, different enough semantics to keep separate).

import Data.Bits
import Data.List

public export
Bytes : Type
Bytes = List Bits8

export
u8 : Nat -> Bits8
u8 n = cast n

export
u16 : Nat -> Bytes
u16 n = [cast (n `div` 256), cast (n `mod` 256)]

export
u24 : Nat -> Bytes
u24 n = [cast (n `div` 65536), cast ((n `div` 256) `mod` 256), cast (n `mod` 256)]

export
decodeU16 : Bytes -> Maybe (Nat, Bytes)
decodeU16 (b0 :: b1 :: rest) = Just (cast b0 * 256 + cast b1, rest)
decodeU16 _                  = Nothing

export
decodeU24 : Bytes -> Maybe (Nat, Bytes)
decodeU24 (b0 :: b1 :: b2 :: rest) = Just (cast b0 * 65536 + cast b1 * 256 + cast b2, rest)
decodeU24 _                        = Nothing

-- A vector with a `lenBytes`-byte big-endian length prefix (RFC 8446's
-- opaque foo<a..b> style, specialized to 1/2-byte length fields since
-- that's all this client's handshake messages use).
export
decodeVec8 : Bytes -> Maybe (Bytes, Bytes)
decodeVec8 (lenB :: rest) =
  let len : Nat
      len = cast lenB
  in if length rest >= len then Just (take len rest, drop len rest) else Nothing
decodeVec8 [] = Nothing

export
decodeVec16 : Bytes -> Maybe (Bytes, Bytes)
decodeVec16 bytes = do
  (len, rest) <- decodeU16 bytes
  if length rest >= len then Just (take len rest, drop len rest) else Nothing

export
encodeVec8 : Bytes -> Bytes
encodeVec8 body = u8 (length body) :: body

export
encodeVec16 : Bytes -> Bytes
encodeVec16 body = u16 (length body) ++ body

-- One TLS extension: a 2-byte type, then a 2-byte-length-prefixed body.
export
encodeExtension : (extType : Nat) -> (body : Bytes) -> Bytes
encodeExtension extType body = u16 extType ++ encodeVec16 body

public export
record RawExtension where
  constructor MkRawExtension
  extType : Nat
  extBody : Bytes

export
decodeExtensions : Bytes -> Maybe (List RawExtension)
decodeExtensions [] = Just []
decodeExtensions bytes = do
  (ty, rest1)   <- decodeU16 bytes
  (body, rest2) <- decodeVec16 rest1
  more          <- decodeExtensions rest2
  pure (MkRawExtension ty body :: more)

export
findExtension : Nat -> List RawExtension -> Maybe Bytes
findExtension ty exts = extBody <$> find (\e => e.extType == ty) exts

-- A handshake message: 1-byte type, 3-byte big-endian length, body.
export
handshakeMessage : (msgType : Nat) -> (body : Bytes) -> Bytes
handshakeMessage msgType body = u8 msgType :: u24 (length body) ++ body

||| Splits the leading complete handshake message off `bytes`, if any is
||| fully present - returns (msgType, body, rest). A handshake message can
||| be smaller than one TLS record or span several; the record layer is
||| responsible for buffering enough bytes before this is called.
export
decodeHandshakeMessage : Bytes -> Maybe (Nat, Bytes, Bytes)
decodeHandshakeMessage (tyB :: rest0) = do
  (len, rest1) <- decodeU24 rest0
  if length rest1 >= len
     then Just (cast tyB, take len rest1, drop len rest1)
     else Nothing
decodeHandshakeMessage [] = Nothing

-- Handshake message type numbers this client cares about (RFC 8446 section 4).
public export
htClientHello, htServerHello, htEncryptedExtensions, htCertificate,
  htCertificateVerify, htFinished, htNewSessionTicket : Nat
htClientHello         = 1
htServerHello         = 2
htEncryptedExtensions = 8
htCertificate         = 11
htCertificateVerify   = 15
htFinished            = 20
htNewSessionTicket    = 4

-- Extension type numbers.
public export
extServerName, extSupportedGroups, extSignatureAlgorithms, extKeyShare,
  extSupportedVersions : Nat
extServerName          = 0
extSupportedGroups     = 10
extSignatureAlgorithms = 13
extKeyShare            = 51
extSupportedVersions   = 43

-- The one named group this client offers/accepts: x25519.
public export
groupX25519 : Nat
groupX25519 = 0x001d
