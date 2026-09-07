module Crypto.P256

-- NIST P-256 (secp256r1) ECDH - required because Postgres's ssl_ecdh_curve
-- setting (be-secure-openssl.c) defaults to "prime256v1" and, in current
-- Postgres/OpenSSL, can only ever name a classic named EC_KEY curve
-- (P-256, P-384, P-521, ...) - not X25519, which OpenSSL exposes through
-- a different key-type API entirely. That was discovered empirically
-- while testing this client's TLS support against a stock `postgres:16`
-- container: even a bare `openssl s_client` offering only x25519 gets a
-- "handshake failure" from it. Crypto.Curve25519 (X25519) is left in
-- place - it's simpler and still a fine building block/reference - but
-- P-256 is what actually interoperates with an unmodified Postgres
-- server, so it's what Network.TLS uses for the real key exchange.
--
-- Affine-coordinate double-and-add, using Idris2's Integer for field
-- arithmetic mod p - same reasoning as Crypto.Curve25519. Not constant-
-- time; see that module's comment for why that tradeoff is accepted here
-- too.

import Data.Bits
import Data.List

-- Computed from its defining formula (FIPS 186-4) rather than hand-typed
-- as a 64-hex-digit literal - a single mistyped digit in a constant that
-- long is exactly the class of bug that's easy to introduce and hard to
-- spot by eye (and did happen here during development: a hand-typed
-- version came up one byte short, silently producing a 248-bit modulus
-- instead of 256-bit and wrong results for every operation built on it).
p256 : Integer
p256 = (2 `pow` 256) - (2 `pow` 224) + (2 `pow` 192) + (2 `pow` 96) - 1
  where
    pow : Integer -> Nat -> Integer
    pow base Z     = 1
    pow base (S k) = base * pow base k

aParam : Integer
aParam = p256 - 3

bParam : Integer
bParam = 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b

gx : Integer
gx = 0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296

gy : Integer
gy = 0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5

data PPoint = Infinity | Affine Integer Integer

fieldAdd : Integer -> Integer -> Integer
fieldAdd x y = (x + y) `mod` p256

fieldSub : Integer -> Integer -> Integer
fieldSub x y = (x - y) `mod` p256

fieldMul : Integer -> Integer -> Integer
fieldMul x y = (x * y) `mod` p256

powMod : Integer -> Integer -> Integer
powMod base0 exp0 = go (base0 `mod` p256) exp0 1
  where
    go : Integer -> Integer -> Integer -> Integer
    go base exp acc =
      if exp <= 0
         then acc
         else let acc'  = if (exp .&. 1) == 1 then fieldMul acc base else acc
                  base' = fieldMul base base
              in go base' (exp `shiftR` 1) acc'

fieldInv : Integer -> Integer
fieldInv x = powMod x (p256 - 2)

pointDouble : PPoint -> PPoint
pointDouble Infinity     = Infinity
pointDouble (Affine x y) =
  if y `mod` p256 == 0
     then Infinity
     else let lambda = fieldMul (fieldAdd (fieldMul 3 (fieldMul x x)) aParam) (fieldInv (fieldMul 2 y))
              x3     = fieldSub (fieldSub (fieldMul lambda lambda) x) x
              y3     = fieldSub (fieldMul lambda (fieldSub x x3)) y
          in Affine x3 y3

pointAdd : PPoint -> PPoint -> PPoint
pointAdd Infinity q        = q
pointAdd p        Infinity = p
pointAdd (Affine x1 y1) (Affine x2 y2) =
  if x1 == x2
     then if (y1 + y2) `mod` p256 == 0
             then Infinity
             else pointDouble (Affine x1 y1)
     else let lambda = fieldMul (fieldSub y2 y1) (fieldInv (fieldSub x2 x1))
              x3     = fieldSub (fieldSub (fieldMul lambda lambda) x1) x2
              y3     = fieldSub (fieldMul lambda (fieldSub x1 x3)) y1
          in Affine x3 y3

-- Right-to-left double-and-add. Correct for any non-negative `k`
-- regardless of whether it's been reduced mod the curve order first -
-- k*P = (k mod n)*P since P has order dividing n.
scalarMul : Integer -> PPoint -> PPoint
scalarMul k0 p0 = go k0 p0 Infinity
  where
    go : Integer -> PPoint -> PPoint -> PPoint
    go k p acc =
      if k <= 0
         then acc
         else let acc' = if (k .&. 1) == 1 then pointAdd acc p else acc
              in go (k `shiftR` 1) (pointDouble p) acc'

decodeBE : List Bits8 -> Integer
decodeBE = foldl (\acc, b => acc `shiftL` 8 .|. cast b) 0

encodeBE32 : Integer -> List Bits8
encodeBE32 n = reverse (go n 32)
  where
    go : Integer -> Nat -> List Bits8
    go _ Z     = []
    go m (S k) = cast (m .&. 0xff) :: go (m `shiftR` 8) k

-- SEC1 uncompressed point format: 0x04 || X (32 bytes BE) || Y (32 bytes BE).
decodeUncompressedPoint : List Bits8 -> Maybe PPoint
decodeUncompressedPoint (0x04 :: rest) =
  if length rest == 64
     then let (xBytes, yBytes) = splitAt 32 rest
          in Just (Affine (decodeBE xBytes) (decodeBE yBytes))
     else Nothing
decodeUncompressedPoint _ = Nothing

encodeUncompressedPoint : PPoint -> List Bits8
encodeUncompressedPoint Infinity     = []
encodeUncompressedPoint (Affine x y) = 0x04 :: encodeBE32 x ++ encodeBE32 y

||| Derives the uncompressed public key point (65 bytes) for a 32-byte
||| big-endian private scalar, by scalar-multiplying the base point.
export
p256PublicKey : (privateKey : List Bits8) -> List Bits8
p256PublicKey privateKey = encodeUncompressedPoint (scalarMul (decodeBE privateKey) (Affine gx gy))

||| RFC 8446 section 4.2.8.2: the ECDHE shared secret for a NIST curve is
||| just the X-coordinate of the resulting point (not the full point, and
||| not hashed). Nothing if `peerPublicKey` isn't a well-formed
||| uncompressed point or the scalar multiplication lands on infinity
||| (which a valid peer key and nonzero private scalar should never do).
export
p256SharedSecret : (privateKey : List Bits8) -> (peerPublicKey : List Bits8) -> Maybe (List Bits8)
p256SharedSecret privateKey peerPublicKey = do
  peerPoint <- decodeUncompressedPoint peerPublicKey
  case scalarMul (decodeBE privateKey) peerPoint of
       Infinity   => Nothing
       Affine x _ => Just (encodeBE32 x)
