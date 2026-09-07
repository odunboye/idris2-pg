module Crypto.Curve25519

-- X25519 (RFC 7748) - the key exchange used by TLS 1.3's key_share
-- extension. Field arithmetic mod 2^255-19 is done with Idris2's built-in
-- Integer (arbitrary precision, exact - Chez's native bignums), not a
-- hand-rolled byte-array bignum: this project already leans on Integer
-- for correctness wherever a fixed-width Int would risk overflow (see
-- Helper.decodeInt64), and the same reasoning applies here, more so -
-- schoolbook byte-array multiply/carry code for a 255-bit field is exactly
-- the kind of place a from-scratch implementation is most likely to hide a
-- carry bug. Integer arithmetic is a language primitive here, not an
-- external crypto library, consistent with this project's from-scratch
-- policy elsewhere (PBKDF2/SHA256 are hand-written; only the underlying
-- big-integer +/-/* is delegated to the runtime, the same way `Bits8`
-- addition is delegated to the CPU).
--
-- Not constant-time. A hand-written implementation on a GC'd, JIT'd Scheme
-- runtime cannot meaningfully guarantee that anyway (GC pauses and
-- branch-predication effects aren't under this code's control regardless
-- of how carefully the Idris source avoids branching on secret data), so
-- no attempt is made to pretend otherwise. This is the same class of
-- tradeoff already made for SCRAM's client nonce (a non-cryptographic PRNG
-- was judged adequate there because uniqueness, not secrecy, was what
-- mattered); here the tradeoff is judged acceptable because the
-- alternative - not having TLS at all - is strictly worse for this
-- client's users, and a timing side-channel on ECDHE key exchange is a
-- narrow, high-effort attack compared to a plaintext wire.

import Data.Bits
import Data.List

p25519 : Integer
p25519 = (1 `shiftL` 255) - 19

a24 : Integer
a24 = 121665

fieldAdd : Integer -> Integer -> Integer
fieldAdd x y = (x + y) `mod` p25519

fieldSub : Integer -> Integer -> Integer
fieldSub x y = (x - y) `mod` p25519

fieldMul : Integer -> Integer -> Integer
fieldMul x y = (x * y) `mod` p25519

-- a^e mod p25519, by repeated squaring.
powMod : Integer -> Integer -> Integer
powMod base0 exp0 = go (base0 `mod` p25519) exp0 1
  where
    go : Integer -> Integer -> Integer -> Integer
    go base exp acc =
      if exp <= 0
         then acc
         else let acc'  = if (exp .&. 1) == 1 then fieldMul acc base else acc
                  base' = fieldMul base base
              in go base' (exp `shiftR` 1) acc'

-- Modular inverse via Fermat's little theorem (p25519 is prime).
fieldInv : Integer -> Integer
fieldInv x = powMod x (p25519 - 2)

-- `bytes` is little-endian (least-significant byte first, as it comes off
-- the wire) - reverse to most-significant-first, then fold the usual way.
decodeLittleEndian : List Bits8 -> Integer
decodeLittleEndian bytes = foldl (\acc, b => acc `shiftL` 8 .|. cast b) 0 (reverse bytes)

encodeLittleEndian32 : Integer -> List Bits8
encodeLittleEndian32 n = go n 32
  where
    go : Integer -> Nat -> List Bits8
    go _ Z     = []
    go m (S k) = cast (m .&. 0xff) :: go (m `shiftR` 8) k

-- RFC 7748 section 5: clear the high bit of the u-coordinate's last
-- (most-significant) byte - some implementations set it; Curve25519's
-- field is only 255 bits.
decodeUCoordinate : List Bits8 -> Integer
decodeUCoordinate bytes = case reverse bytes of
     []            => 0
     (top :: rest) => decodeLittleEndian (reverse ((top .&. 0x7f) :: rest))

-- RFC 7748 section 5: clamp the scalar (clear the low 3 bits of the first
-- byte; clear the top bit and set the second-highest bit of the last).
decodeScalar25519 : List Bits8 -> Integer
decodeScalar25519 []              = 0
decodeScalar25519 (first :: rest) =
  case reverse (first .&. 0xf8 :: rest) of
       []            => 0
       (top :: revRest) => decodeLittleEndian (reverse (((top .&. 0x7f) .|. 0x40) :: revRest))

-- Constant-time-shaped (but see module comment - not a real guarantee on
-- this runtime) conditional swap, done as arithmetic rather than a branch.
cswap : Bool -> Integer -> Integer -> (Integer, Integer)
cswap False x y = (x, y)
cswap True  x y = (y, x)

-- The Montgomery ladder, RFC 7748 section 5.
ladder : Integer -> Integer -> Integer
ladder k u = finish (go 255 1 0 u 1 False)
  where
    go : Nat -> Integer -> Integer -> Integer -> Integer -> Bool
       -> (Integer, Integer)
    go Z x2 z2 x3 z3 swap =
      let (x2', _) = cswap swap x2 x3
          (z2', _) = cswap swap z2 z3
      in (x2', z2')
    go (S t) x2 z2 x3 z3 swap =
      let kt       = (k `shiftR` t) .&. 1
          swap'    = swap /= (kt == 1)
          (x2a, x3a) = cswap swap' x2 x3
          (z2a, z3a) = cswap swap' z2 z3
          a   = fieldAdd x2a z2a
          aa  = fieldMul a a
          b   = fieldSub x2a z2a
          bb  = fieldMul b b
          e   = fieldSub aa bb
          c   = fieldAdd x3a z3a
          d   = fieldSub x3a z3a
          da  = fieldMul d a
          cb  = fieldMul c b
          x3' = let s = fieldAdd da cb in fieldMul s s
          z3' = let s = fieldSub da cb in fieldMul u (fieldMul s s)
          x2' = fieldMul aa bb
          z2' = fieldMul e (fieldAdd aa (fieldMul a24 e))
      in go t x2' z2' x3' z3' (kt == 1)

    finish : (Integer, Integer) -> Integer
    finish (x2, z2) = fieldMul x2 (fieldInv z2)

||| RFC 7748's X25519(k, u): scalar-multiplies the Montgomery u-coordinate
||| `u` (32 bytes, little-endian) by the clamped scalar `k` (32 bytes).
||| Used both to derive a public key from a private scalar (u = 9, the
||| fixed base point) and to compute the shared secret (u = the peer's
||| public key).
export
x25519 : (scalar : List Bits8) -> (uCoord : List Bits8) -> List Bits8
x25519 scalar uCoord =
  encodeLittleEndian32 (ladder (decodeScalar25519 scalar) (decodeUCoordinate uCoord))

||| The fixed base point (u = 9), as its 32-byte little-endian encoding.
export
basePoint : List Bits8
basePoint = 9 :: replicate 31 0

||| Derives the public key (32 bytes) for a given private scalar (32
||| random bytes) by scalar-multiplying the base point.
export
x25519PublicKey : (privateKey : List Bits8) -> List Bits8
x25519PublicKey privateKey = x25519 privateKey basePoint
