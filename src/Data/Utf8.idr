module Data.Utf8

-- A small, from-scratch, dependency-free UTF-8 codec, shared by anything
-- that needs to turn a String into bytes or back "for real" - i.e. not
-- Idris2's Cast Char Bits8/Cast Bits8 Char, which do a Latin-1-style
-- byte-per-codepoint mapping that corrupts any codepoint above 0x7F.
-- Postgres's default client_encoding is UTF8, and this matters wherever a
-- password, parameter, or column value can contain non-ASCII text -
-- originally added in Helper (the wire-encoding path) and moved here so
-- Crypto.SCRAM/Crypto.MD5 (password hashing) can use the same codec
-- without creating an import cycle back through Helper.

import Data.Bits
import Data.List

encodeUtf8Char : Char -> List Bits8
encodeUtf8Char c =
  let cp = ord c
  in if cp < 0x80 then [cast cp]
     else if cp < 0x800 then
       [ cast (0xC0 .|. (cp `shiftR` 6))
       , cast (0x80 .|. (cp .&. 0x3F))
       ]
     else if cp < 0x10000 then
       [ cast (0xE0 .|. (cp `shiftR` 12))
       , cast (0x80 .|. ((cp `shiftR` 6) .&. 0x3F))
       , cast (0x80 .|. (cp .&. 0x3F))
       ]
     else
       [ cast (0xF0 .|. (cp `shiftR` 18))
       , cast (0x80 .|. ((cp `shiftR` 12) .&. 0x3F))
       , cast (0x80 .|. ((cp `shiftR` 6) .&. 0x3F))
       , cast (0x80 .|. (cp .&. 0x3F))
       ]

||| Raw UTF-8 bytes for a String.
public export
stringToBytes : String -> List Bits8
stringToBytes s = concatMap encodeUtf8Char (unpack s)

-- U+FFFD, substituted for a malformed/truncated byte sequence rather than
-- failing outright - bytesToString is used pervasively as a total
-- String-returning function, and its callers trust their byte source to
-- send well-formed UTF-8 in practice; this only kicks in on genuinely
-- corrupt input.
replacementChar : Char
replacementChar = chr 0xFFFD

decodeUtf8 : List Bits8 -> List Char
decodeUtf8 [] = []
decodeUtf8 (b :: bs) =
  if b < 0x80
     then chr (cast b) :: decodeUtf8 bs
  else if (b .&. 0xE0) == 0xC0
     then case bs of
               (b1 :: rest) =>
                 chr (((cast b .&. 0x1F) `shiftL` 6) .|. (cast b1 .&. 0x3F)) :: decodeUtf8 rest
               [] => [replacementChar]
  else if (b .&. 0xF0) == 0xE0
     then case bs of
               (b1 :: b2 :: rest) =>
                 chr (((cast b .&. 0x0F) `shiftL` 12) .|. ((cast b1 .&. 0x3F) `shiftL` 6) .|. (cast b2 .&. 0x3F))
                   :: decodeUtf8 rest
               _ => [replacementChar]
  else if (b .&. 0xF8) == 0xF0
     then case bs of
               (b1 :: b2 :: b3 :: rest) =>
                 chr (((cast b .&. 0x07) `shiftL` 18) .|. ((cast b1 .&. 0x3F) `shiftL` 12)
                       .|. ((cast b2 .&. 0x3F) `shiftL` 6) .|. (cast b3 .&. 0x3F))
                   :: decodeUtf8 rest
               _ => [replacementChar]
  else replacementChar :: decodeUtf8 bs

||| Decodes UTF-8 bytes into a String, substituting U+FFFD for any
||| malformed/truncated sequence rather than failing.
public export
bytesToString : List Bits8 -> String
bytesToString bs = pack (decodeUtf8 bs)
