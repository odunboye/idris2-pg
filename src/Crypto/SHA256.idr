module Crypto.SHA256

-- Pure-Idris SHA-256 (FIPS 180-4), needed for SCRAM-SHA-256 authentication
-- (HMAC-SHA256 and PBKDF2 are built on top of this in Crypto.SCRAM). Same
-- rationale as Crypto.MD5: no hash library exists anywhere in this
-- workspace to depend on.

import Data.Bits
import Data.Fin
import Data.List

%default covering

rotr32 : Bits32 -> Nat -> Bits32
rotr32 x n =
  (x `shiftR` restrict 31 (cast n)) .|. (x `shiftL` restrict 31 (cast (32 `minus` n)))

kTable : List Bits32
kTable =
  [ 0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5
  , 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174
  , 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da
  , 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967
  , 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85
  , 0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070
  , 0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3
  , 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
  ]

getAt : Bits32 -> Int -> List Bits32 -> Bits32
getAt def _ [] = def
getAt def 0 (x :: _) = x
getAt def n (_ :: xs) = if n <= 0 then def else getAt def (n - 1) xs

buildSchedule : List Bits32 -> List Bits32
buildSchedule w16 = go w16 16
  where
    go : List Bits32 -> Int -> List Bits32
    go ws i =
      if i >= 64
         then ws
         else
           let w15  = getAt 0 (i - 15) ws
               w2   = getAt 0 (i - 2) ws
               w16' = getAt 0 (i - 16) ws
               w7   = getAt 0 (i - 7) ws
               s0 = rotr32 w15 7 `xor` rotr32 w15 18 `xor` (w15 `shiftR` 3)
               s1 = rotr32 w2 17 `xor` rotr32 w2 19 `xor` (w2 `shiftR` 10)
               wi = w16' + s0 + w7 + s1
           in go (ws ++ [wi]) (i + 1)

chFn : Bits32 -> Bits32 -> Bits32 -> Bits32
chFn e f g = (e .&. f) `xor` (complement e .&. g)

majFn : Bits32 -> Bits32 -> Bits32 -> Bits32
majFn a b c = (a .&. b) `xor` (a .&. c) `xor` (b .&. c)

record ShaState where
  constructor MkShaState
  sA, sB, sC, sD, sE, sF, sG, sH : Bits32

shaRound : List Bits32 -> Int -> ShaState -> ShaState
shaRound w i st@(MkShaState a b c d e f g h) =
  if i >= 64
     then st
     else
       let bigS1 = rotr32 e 6 `xor` rotr32 e 11 `xor` rotr32 e 25
           ch    = chFn e f g
           ki    = getAt 0 i kTable
           wi    = getAt 0 i w
           temp1 = h + bigS1 + ch + ki + wi
           bigS0 = rotr32 a 2 `xor` rotr32 a 13 `xor` rotr32 a 22
           maj   = majFn a b c
           temp2 = bigS0 + maj
       in shaRound w (i + 1) (MkShaState (temp1 + temp2) a b c (d + temp1) e f g)

compress : ShaState -> List Bits32 -> ShaState
compress st0 w16 =
  let w  = buildSchedule w16
      st1 = shaRound w 0 st0
  in MkShaState (sA st0 + sA st1) (sB st0 + sB st1) (sC st0 + sC st1) (sD st0 + sD st1)
                (sE st0 + sE st1) (sF st0 + sF st1) (sG st0 + sG st1) (sH st0 + sH st1)

wordsBE : List Bits8 -> List Bits32
wordsBE (b0 :: b1 :: b2 :: b3 :: rest) =
  let w : Bits32
      w = (cast b0 `shiftL` 24) .|. (cast b1 `shiftL` 16) .|. (cast b2 `shiftL` 8) .|. cast b3
  in w :: wordsBE rest
wordsBE _ = []

chunksOf64 : List Bits8 -> List (List Bits8)
chunksOf64 [] = []
chunksOf64 xs = take 64 xs :: chunksOf64 (drop 64 xs)

-- Big-endian byte extraction of the low `n` bytes of an Int (SHA appends a
-- big-endian bit-length, unlike MD5's little-endian one).
beBytesN : Nat -> Int -> List Bits8
beBytesN k n = reverse (go k n)
  where
    go : Nat -> Int -> List Bits8
    go Z _ = []
    go (S j) m = fromInteger (cast (m `mod` 256)) :: go j (m `div` 256)

word32BEBytes : Bits32 -> List Bits8
word32BEBytes w =
  [ cast ((w `shiftR` 24) .&. 0xff)
  , cast ((w `shiftR` 16) .&. 0xff)
  , cast ((w `shiftR` 8) .&. 0xff)
  , cast (w .&. 0xff)
  ]

shaPad : List Bits8 -> List Bits8
shaPad msg =
  let msgLenBits : Int = cast (length msg) * 8
      withOne = msg ++ [0x80]
      r : Int
      r = cast (length withOne) `mod` 64
      padLen : Int
      padLen = if r <= 56 then 56 - r else 120 - r
      padded = withOne ++ replicate (cast padLen) 0
  in padded ++ beBytesN 8 msgLenBits

||| 32-byte SHA-256 digest.
public export
sha256 : List Bits8 -> List Bits8
sha256 msg =
  let blocks = map wordsBE (chunksOf64 (shaPad msg))
      initial = MkShaState 0x6a09e667 0xbb67ae85 0x3c6ef372 0xa54ff53a
                            0x510e527f 0x9b05688c 0x1f83d9ab 0x5be0cd19
      final = foldl compress initial blocks
  in concatMap word32BEBytes
       [sA final, sB final, sC final, sD final, sE final, sF final, sG final, sH final]
