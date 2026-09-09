module Crypto.ChaCha20Poly1305

-- The ChaCha20-Poly1305 AEAD construction (RFC 8439 section 2.8) - this is
-- the actual cipher TLS 1.3's record layer uses (TLS_CHACHA20_POLY1305_
-- SHA256), combining Crypto.ChaCha20 and Crypto.Poly1305.

import Crypto.ChaCha20
import Crypto.Poly1305
import Data.Bits
import Data.List

le64 : Nat -> List Bits8
le64 n = go n 8
  where
    go : Nat -> Nat -> List Bits8
    go _     Z     = []
    go m (S k) = cast (m `mod` 256) :: go (m `div` 256) k

-- Zero-pad to the next multiple of 16 bytes (RFC 8439's pad16).
pad16 : List Bits8 -> List Bits8
pad16 xs = replicate ((16 `minus` (length xs `mod` 16)) `mod` 16) 0

-- RFC 8439 section 2.6: the one-time Poly1305 key is the first 32 bytes of
-- the ChaCha20 keystream at counter 0 (block 1 onward is the actual
-- ciphertext keystream, so a (key, nonce) pair's block 0 must never be
-- reused for anything else).
poly1305KeyGen : (key : List Bits8) -> (nonce : List Bits8) -> List Bits8
poly1305KeyGen key nonce = chacha20 key 0 nonce (replicate 32 0)

macData : (aad : List Bits8) -> (ciphertext : List Bits8) -> List Bits8
macData aad ciphertext =
  aad ++ pad16 aad ++ ciphertext ++ pad16 ciphertext
    ++ le64 (length aad) ++ le64 (length ciphertext)

-- Not short-circuiting on the first differing byte, unlike a naive `==`
-- on the two lists - some nod to avoiding a timing oracle on tag
-- verification, though see the caveats already documented in
-- Crypto.Curve25519 about what this runtime can and can't actually
-- guarantee. Exported since Network.TLS's Finished check and
-- Crypto.SCRAM's server-signature check need the same property.
export
constantTimeEq : List Bits8 -> List Bits8 -> Bool
constantTimeEq xs ys =
  length xs == length ys && foldl xor 0 (zipWith xor xs ys) == 0

||| Encrypts `plaintext` under `key` (32 bytes) and `nonce` (12 bytes),
||| authenticating `aad` alongside it. Returns (ciphertext, 16-byte tag).
||| `nonce` must never repeat for a given key (TLS 1.3 derives it from a
||| static IV XORed with the record sequence number - see Network.TLS).
export
encrypt : (key : List Bits8) -> (nonce : List Bits8) -> (aad : List Bits8) -> (plaintext : List Bits8)
        -> (List Bits8, List Bits8)
encrypt key nonce aad plaintext =
  let otk        = poly1305KeyGen key nonce
      ciphertext = chacha20 key 1 nonce plaintext
      tag        = poly1305 otk (macData aad ciphertext)
  in (ciphertext, tag)

||| Verifies `tag` and decrypts `ciphertext`, or Nothing if the tag doesn't
||| match (a corrupted or tampered record - the caller must treat this as
||| fatal to the connection, not skip the record, per RFC 8446 section 5.2).
export
decrypt : (key : List Bits8) -> (nonce : List Bits8) -> (aad : List Bits8)
        -> (ciphertext : List Bits8) -> (tag : List Bits8) -> Maybe (List Bits8)
decrypt key nonce aad ciphertext tag =
  let otk         = poly1305KeyGen key nonce
      expectedTag = poly1305 otk (macData aad ciphertext)
  in if constantTimeEq expectedTag tag
        then Just (chacha20 key 1 nonce ciphertext)
        else Nothing
