module Crypto.HKDF

-- HKDF (RFC 5869) built on the HMAC-SHA256 already implemented for SCRAM
-- (Crypto.SCRAM.hmacSha256), plus TLS 1.3's HKDF-Expand-Label and
-- Derive-Secret (RFC 8446 section 7.1) built on top of that - these are
-- how every TLS 1.3 traffic secret (handshake and application, both
-- directions) is derived from the shared ECDHE secret.

import Crypto.SCRAM
import Data.Bits
import Data.List

strBytes : String -> List Bits8
strBytes s = map (cast . ord) (unpack s)

||| HKDF-Extract (RFC 5869 section 2.2): PRK = HMAC-Hash(salt, IKM).
export
hkdfExtract : (salt : List Bits8) -> (ikm : List Bits8) -> List Bits8
hkdfExtract salt ikm = hmacSha256 salt ikm

||| HKDF-Expand (RFC 5869 section 2.3): derives `len` bytes of output
||| keying material from a pseudorandom key `prk` and context `info`.
export
hkdfExpand : (prk : List Bits8) -> (info : List Bits8) -> (len : Nat) -> List Bits8
hkdfExpand prk info len = take len (go [] 1 neededBlocks)
  where
    -- SHA-256's output is 32 bytes per block (RFC 5869's HashLen).
    neededBlocks : Nat
    neededBlocks = (len + 31) `div` 32

    go : List Bits8 -> Bits8 -> Nat -> List Bits8
    go _     _       Z     = []
    go tPrev counter (S k) =
      let tCur = hmacSha256 prk (tPrev ++ info ++ [counter])
      in tCur ++ go tCur (counter + 1) k

-- RFC 8446 section 7.1's HkdfLabel struct:
--   uint16 length; opaque label<7..255> = "tls13 " ++ label; opaque context<0..255>
-- both `label` (with prefix) and `context` are always well under 256
-- bytes for every use in this client, so a single-byte length prefix is
-- always sufficient (matches the wire format's own 1-byte length field).
hkdfLabelStruct : (label : String) -> (context : List Bits8) -> (length : Nat) -> List Bits8
hkdfLabelStruct label context length =
  let fullLabel = strBytes ("tls13 " ++ label)
      lengthBE  = [cast (length `div` 256), cast (length `mod` 256)]
  in lengthBE ++ [cast (List.length fullLabel)] ++ fullLabel
              ++ [cast (List.length context)] ++ context

||| RFC 8446 section 7.1's HKDF-Expand-Label: HKDF-Expand keyed by a
||| structured label (prefixed "tls13 ") and context, rather than a raw
||| info string - this is what actually derives every TLS 1.3 secret.
export
hkdfExpandLabel : (secret : List Bits8) -> (label : String) -> (context : List Bits8) -> (length : Nat) -> List Bits8
hkdfExpandLabel secret label context length =
  hkdfExpand secret (hkdfLabelStruct label context length) length

||| RFC 8446 section 7.1's Derive-Secret: HKDF-Expand-Label with the
||| context set to a transcript hash (the caller computes this - see
||| Network.TLS - since it's just Crypto.SHA256.sha256 over the handshake
||| messages seen so far) and length fixed at SHA-256's 32-byte output.
export
deriveSecret : (secret : List Bits8) -> (label : String) -> (transcriptHash : List Bits8) -> List Bits8
deriveSecret secret label transcriptHash = hkdfExpandLabel secret label transcriptHash 32
