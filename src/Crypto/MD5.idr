module Crypto.MD5

-- Pure-Idris MD5 (RFC 1321), used only for Postgres's md5 password
-- authentication ("md5" ++ hex(md5(hex(md5(password ++ user)) ++ salt))).
-- No cryptographic library exists anywhere in this workspace to depend on,
-- and MD5 is not used here for any security-sensitive purpose beyond
-- matching a legacy wire protocol.

import Data.Bits
import Data.Fin
import Data.List
import Data.Utf8

%default covering

-- Bits32's shiftL/shiftR take a `Fin 32` index. Round shift amounts are
-- known at compile time (7,12,17,22,...) so those work as plain integer
-- literals, but the left-rotate amount is looked up at runtime from a
-- table, so it needs `restrict` to build the `Fin 32`.
rotl32 : Bits32 -> Nat -> Bits32
rotl32 x n =
  (x `shiftL` restrict 31 (cast n)) .|. (x `shiftR` restrict 31 (cast (32 `minus` n)))

sTable : List Nat
sTable =
  [ 7, 12, 17, 22,  7, 12, 17, 22,  7, 12, 17, 22,  7, 12, 17, 22
  , 5,  9, 14, 20,  5,  9, 14, 20,  5,  9, 14, 20,  5,  9, 14, 20
  , 4, 11, 16, 23,  4, 11, 16, 23,  4, 11, 16, 23,  4, 11, 16, 23
  , 6, 10, 15, 21,  6, 10, 15, 21,  6, 10, 15, 21,  6, 10, 15, 21
  ]

kTable : List Bits32
kTable =
  [ 0xd76aa478, 0xe8c7b756, 0x242070db, 0xc1bdceee
  , 0xf57c0faf, 0x4787c62a, 0xa8304613, 0xfd469501
  , 0x698098d8, 0x8b44f7af, 0xffff5bb1, 0x895cd7be
  , 0x6b901122, 0xfd987193, 0xa679438e, 0x49b40821
  , 0xf61e2562, 0xc040b340, 0x265e5a51, 0xe9b6c7aa
  , 0xd62f105d, 0x02441453, 0xd8a1e681, 0xe7d3fbc8
  , 0x21e1cde6, 0xc33707d6, 0xf4d50d87, 0x455a14ed
  , 0xa9e3e905, 0xfcefa3f8, 0x676f02d9, 0x8d2a4c8a
  , 0xfffa3942, 0x8771f681, 0x6d9d6122, 0xfde5380c
  , 0xa4beea44, 0x4bdecfa9, 0xf6bb4b60, 0xbebfbc70
  , 0x289b7ec6, 0xeaa127fa, 0xd4ef3085, 0x04881d05
  , 0xd9d4d039, 0xe6db99e5, 0x1fa27cf8, 0xc4ac5665
  , 0xf4292244, 0x432aff97, 0xab9423a7, 0xfc93a039
  , 0x655b59c3, 0x8f0ccc92, 0xffeff47d, 0x85845dd1
  , 0x6fa87e4f, 0xfe2ce6e0, 0xa3014314, 0x4e0811a1
  , 0xf7537e82, 0xbd3af235, 0x2ad7d2bb, 0xeb86d391
  ]

getAtD : a -> Int -> List a -> a
getAtD def _ [] = def
getAtD def 0 (x :: _) = x
getAtD def n (_ :: xs) = if n <= 0 then def else getAtD def (n - 1) xs

sAt : Int -> Nat
sAt i = getAtD 7 i sTable

kAt : Int -> Bits32
kAt i = getAtD 0 i kTable

-- One MD5 round; `m` is the current block's 16 little-endian 32-bit words.
mdRound : List Bits32 -> Int -> (Bits32, Bits32, Bits32, Bits32) -> (Bits32, Bits32, Bits32, Bits32)
mdRound m i st@(a, b, c, d) =
  if i >= 64
     then st
     else
       let (f, g) =
             if i < 16      then ((b .&. c) .|. (complement b .&. d), i)
             else if i < 32 then ((d .&. b) .|. (complement d .&. c), (5 * i + 1) `mod` 16)
             else if i < 48 then (b `xor` c `xor` d, (3 * i + 5) `mod` 16)
             else                (c `xor` (b .|. complement d), (7 * i) `mod` 16)
           f' = f + a + kAt i + getAtD 0 g m
           newB = b + rotl32 f' (sAt i)
       in mdRound m (i + 1) (d, newB, b, c)

processBlock : (Bits32, Bits32, Bits32, Bits32) -> List Bits32 -> (Bits32, Bits32, Bits32, Bits32)
processBlock (a0, b0, c0, d0) m =
  let (a, b, c, d) = mdRound m 0 (a0, b0, c0, d0)
  in (a0 + a, b0 + b, c0 + c, d0 + d)

wordsLE : List Bits8 -> List Bits32
wordsLE (b0 :: b1 :: b2 :: b3 :: rest) =
  let w : Bits32
      w = cast b0
            .|. (cast b1 `shiftL` 8)
            .|. (cast b2 `shiftL` 16)
            .|. (cast b3 `shiftL` 24)
  in w :: wordsLE rest
wordsLE _ = []

chunksOf64 : List Bits8 -> List (List Bits8)
chunksOf64 [] = []
chunksOf64 xs = take 64 xs :: chunksOf64 (drop 64 xs)

-- little-endian byte extraction of the low `n` bytes of an Int
leBytesN : Nat -> Int -> List Bits8
leBytesN Z _ = []
leBytesN (S k) n = fromInteger (cast (n `mod` 256)) :: leBytesN k (n `div` 256)

word32LEBytes : Bits32 -> List Bits8
word32LEBytes w =
  [ cast (w .&. 0xff)
  , cast ((w `shiftR` 8) .&. 0xff)
  , cast ((w `shiftR` 16) .&. 0xff)
  , cast ((w `shiftR` 24) .&. 0xff)
  ]

md5Pad : List Bits8 -> List Bits8
md5Pad msg =
  let msgLenBits : Int = cast (length msg) * 8
      withOne = msg ++ [0x80]
      r : Int
      r = (cast (length withOne)) `mod` 64
      padLen : Int
      padLen = if r <= 56 then 56 - r else 120 - r
      padded = withOne ++ replicate (cast padLen) 0
      lenBytes = leBytesN 8 msgLenBits
  in padded ++ lenBytes

||| 16-byte MD5 digest of the given bytes.
public export
md5 : List Bits8 -> List Bits8
md5 msg =
  let blocks = map wordsLE (chunksOf64 (md5Pad msg))
      (a, b, c, d) = foldl processBlock (0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476) blocks
  in word32LEBytes a ++ word32LEBytes b ++ word32LEBytes c ++ word32LEBytes d

||| Lowercase hex encoding of a byte string.
public export
toHex : List Bits8 -> String
toHex bytes = pack (concatMap byteHex bytes)
  where
    hexDigit : Bits8 -> Char
    hexDigit b = if b < 10 then chr (cast b + ord '0') else chr (cast b - 10 + ord 'a')
    byteHex : Bits8 -> List Char
    byteHex b = [ hexDigit (b `shiftR` 4), hexDigit (b .&. 0xf) ]

||| Postgres md5 auth: "md5" ++ hex(md5(hex(md5(password ++ user)) ++ salt))
||| password ++ user goes through the real UTF-8 codec (Data.Utf8), not a
||| per-Char truncating cast - Postgres usernames/passwords aren't limited
||| to ASCII. `inner` itself is always a hex string (ASCII-only by
||| construction), so its own encoding for the outer hash can't matter
||| either way.
public export
pgMD5Password : (password : String) -> (user : String) -> (salt : List Bits8) -> String
pgMD5Password password user salt =
  let inner = toHex (md5 (stringToBytes (password ++ user)))
      outer = toHex (md5 (map (cast . ord) (unpack inner) ++ salt))
  in "md5" ++ outer
