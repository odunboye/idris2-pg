module Data.PGBinary

import Data.PGTypes
import Data.Bits
import Helper

-- Binary-format wire decoding for the value types this client supports in
-- binary mode. See Idris2_pg.queryRowsBinary's doc comment for the caveats
-- (binary formats don't self-describe their type the way text does, so a
-- type mismatch here doesn't fail as cleanly as it does in text mode).

public export
decodeBinaryInt : Bytes -> Either String Int
decodeBinaryInt bytes = case length bytes of
     2 => map fst (decodeInt16 bytes)
     4 => map fst (decodeInt32 bytes)
     8 => map fst (decodeInt64 bytes)
     n => Left ("unexpected byte width for a binary integer: " ++ show n)

public export
decodeBinaryBool : Bytes -> Either String Bool
decodeBinaryBool [n] = Right (n /= 0)
decodeBinaryBool bytes = Left ("expected exactly 1 byte for a binary boolean, got " ++ show (length bytes))

decodeBits32BE : Bytes -> Maybe Bits32
decodeBits32BE [b1, b2, b3, b4] =
  Just ((cast b1 `shiftL` 24) .|. (cast b2 `shiftL` 16) .|. (cast b3 `shiftL` 8) .|. cast b4)
decodeBits32BE _ = Nothing

decodeBits64BE : Bytes -> Maybe Bits64
decodeBits64BE [b1, b2, b3, b4, b5, b6, b7, b8] =
  Just ((cast b1 `shiftL` 56) .|. (cast b2 `shiftL` 48) .|. (cast b3 `shiftL` 40) .|. (cast b4 `shiftL` 32)
          .|. (cast b5 `shiftL` 24) .|. (cast b6 `shiftL` 16) .|. (cast b7 `shiftL` 8) .|. cast b8)
decodeBits64BE _ = Nothing

pow2 : Int -> Double
pow2 n = if n >= 0 then powUp n 1.0 else 1.0 / powUp (-n) 1.0
  where
    powUp : Int -> Double -> Double
    powUp 0 acc = acc
    powUp k acc = powUp (k - 1) (acc * 2.0)

-- IEEE754 decoding computed directly (extract sign/exponent/mantissa, exact
-- power-of-two scaling) rather than via a bit-cast trick, since Idris2 has
-- no 32-bit-float buffer primitive to lean on. Verified against Python's
-- struct.pack reference bit patterns (0/1/-1/pi/subnormal-range/very large
-- and small magnitudes/+-infinity/NaN) before landing.
float32ToDouble : Bits32 -> Double
float32ToDouble bits =
  let signBit  = (bits `shiftR` 31) .&. 1
      expBits  = (bits `shiftR` 23) .&. 0xFF
      mantBits = bits .&. 0x7FFFFF
      sign     = if signBit == 1 then -1.0 else 1.0
      mantissa = cast {to=Double} (cast {to=Int} mantBits) / 8388608.0
  in if expBits == 0
        then if mantBits == 0 then sign * 0.0 else sign * mantissa * pow2 (-126)
        else if expBits == 0xFF
                then if mantBits == 0 then sign * (1.0 / 0.0) else (0.0 / 0.0)
                else sign * (1.0 + mantissa) * pow2 (cast {to=Int} expBits - 127)

float64ToDouble : Bits64 -> Double
float64ToDouble bits =
  let signBit  = (bits `shiftR` 63) .&. 1
      expBits  = (bits `shiftR` 52) .&. 0x7FF
      mantBits = bits .&. 0xFFFFFFFFFFFFF
      sign     = if signBit == 1 then -1.0 else 1.0
      mantissa = cast {to=Double} (cast {to=Int} mantBits) / 4503599627370496.0
  in if expBits == 0
        then if mantBits == 0 then sign * 0.0 else sign * mantissa * pow2 (-1022)
        else if expBits == 0x7FF
                then if mantBits == 0 then sign * (1.0 / 0.0) else (0.0 / 0.0)
                else sign * (1.0 + mantissa) * pow2 (cast {to=Int} expBits - 1023)

public export
decodeBinaryDouble : Bytes -> Either String Double
decodeBinaryDouble bytes = case length bytes of
     4 => case decodeBits32BE bytes of
               Just bits => Right (float32ToDouble bits)
               Nothing   => Left "internal error decoding binary float4"
     8 => case decodeBits64BE bytes of
               Just bits => Right (float64ToDouble bits)
               Nothing   => Left "internal error decoding binary float8"
     n => Left ("unexpected byte width for a binary double: " ++ show n)
