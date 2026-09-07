module Crypto.Poly1305

-- Poly1305 (RFC 8439 section 2.5), the MAC half of ChaCha20-Poly1305.
-- Arithmetic mod 2^130-5 uses Idris2's Integer, for the same reason as
-- Crypto.Curve25519's field arithmetic - see that module's comment.

import Data.Bits
import Data.List

pPoly : Integer
pPoly = (1 `shiftL` 130) - 5

-- RFC 8439: clear specific bits of r so multiplication can't overflow the
-- accumulator's expected range.
clampR : Integer -> Integer
clampR r = r .&. 0x0ffffffc0ffffffc0ffffffc0fffffff

decodeLE : List Bits8 -> Integer
decodeLE bytes = foldl (\acc, b => acc `shiftL` 8 .|. cast b) 0 (reverse bytes)

encodeLE16 : Integer -> List Bits8
encodeLE16 n = go n 16
  where
    go : Integer -> Nat -> List Bits8
    go _ Z     = []
    go m (S k) = cast (m .&. 0xff) :: go (m `shiftR` 8) k

chunksOf16 : List Bits8 -> List (List Bits8)
chunksOf16 [] = []
chunksOf16 xs = take 16 xs :: chunksOf16 (drop 16 xs)

-- A message block (up to 16 bytes) is read as a little-endian integer with
-- an extra 1-bit appended just past its last byte - RFC 8439 calls this
-- "adding one bit beyond the number of octets"; for a full 16-byte block
-- that's bit 128 (0x01 as byte 17), for a shorter final block it's
-- correspondingly lower.
blockValue : List Bits8 -> Integer
blockValue block = decodeLE block .|. (1 `shiftL` (8 * length block))

||| Computes the 16-byte Poly1305 tag for `message` under `key` (32 bytes:
||| the first 16 are r, the last 16 are s, per RFC 8439). One-time-key MAC
||| - a (key, nonce) pair must never be reused across messages, which
||| Crypto.ChaCha20Poly1305 enforces by deriving a fresh Poly1305 key from
||| ChaCha20 block 0 of each AEAD invocation.
export
poly1305 : (key : List Bits8) -> (message : List Bits8) -> List Bits8
poly1305 key message =
  let r  = clampR (decodeLE (take 16 key))
      s  = decodeLE (take 16 (drop 16 key))
      a  = foldl (\acc, block => ((acc + blockValue block) * r) `mod` pPoly) 0 (chunksOf16 message)
      tag = (a + s) `mod` (1 `shiftL` 128)
  in encodeLE16 tag
