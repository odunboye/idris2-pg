module Crypto.ChaCha20

-- ChaCha20 (RFC 8439 section 2), the stream cipher half of the
-- ChaCha20-Poly1305 AEAD used by TLS 1.3's record layer. Chosen over
-- AES-GCM for this from-scratch project because it's built entirely from
-- 32-bit add/rotate/xor - no S-box lookup table or GF(2^8) field
-- arithmetic to get subtly wrong, unlike AES.

import Data.Bits
import Data.Fin
import Data.List
import Data.Vect

rotl32 : Bits32 -> Nat -> Bits32
rotl32 x n =
  (x `shiftL` restrict 31 (cast n)) .|. (x `shiftR` restrict 31 (cast (32 `minus` n)))

State : Type
State = Vect 16 Bits32

quarterRound : Fin 16 -> Fin 16 -> Fin 16 -> Fin 16 -> State -> State
quarterRound ia ib ic id st =
  let a0 = index ia st; b0 = index ib st; c0 = index ic st; d0 = index id st
      a1 = a0 + b0;  d1 = rotl32 (d0 `xor` a1) 16
      c1 = c0 + d1;  b1 = rotl32 (b0 `xor` c1) 12
      a2 = a1 + b1;  d2 = rotl32 (d1 `xor` a2) 8
      c2 = c1 + d2;  b2 = rotl32 (b1 `xor` c2) 7
  in replaceAt ia a2 (replaceAt ib b2 (replaceAt ic c2 (replaceAt id d2 st)))

-- One "double round" (RFC 8439): a column round over (0,4,8,12) etc.,
-- then a diagonal round over (0,5,10,15) etc. 10 double-rounds = the
-- full 20 ChaCha20 rounds.
doubleRound : State -> State
doubleRound st =
  let st1 = quarterRound 0 4 8  12 st
      st2 = quarterRound 1 5 9  13 st1
      st3 = quarterRound 2 6 10 14 st2
      st4 = quarterRound 3 7 11 15 st3
      st5 = quarterRound 0 5 10 15 st4
      st6 = quarterRound 1 6 11 12 st5
      st7 = quarterRound 2 7 8  13 st6
  in quarterRound 3 4 9 14 st7

applyN : Nat -> (a -> a) -> a -> a
applyN Z     _ x = x
applyN (S k) f x = applyN k f (f x)

word32LEBytes : Bits32 -> List Bits8
word32LEBytes w =
  [ cast (w .&. 0xff)
  , cast ((w `shiftR` 8) .&. 0xff)
  , cast ((w `shiftR` 16) .&. 0xff)
  , cast ((w `shiftR` 24) .&. 0xff)
  ]

wordsLE : List Bits8 -> List Bits32
wordsLE (b0 :: b1 :: b2 :: b3 :: rest) =
  let w : Bits32
      w = cast b0 .|. (cast b1 `shiftL` 8) .|. (cast b2 `shiftL` 16) .|. (cast b3 `shiftL` 24)
  in w :: wordsLE rest
wordsLE _ = []

constants : Vect 4 Bits32
constants = [0x61707865, 0x3320646e, 0x79622d32, 0x6b206574]

-- The ChaCha20 block function (RFC 8439 section 2.3): produces 64 bytes
-- of keystream for one (key, counter, nonce) combination.
chachaBlock : (key : Vect 8 Bits32) -> (counter : Bits32) -> (nonce : Vect 3 Bits32) -> List Bits8
chachaBlock key counter nonce =
  let initial : State
      initial = constants ++ key ++ [counter] ++ nonce
      final   = applyN 10 doubleRound initial
      added   = zipWith (+) initial final
  in concatMap word32LEBytes (toList added)

-- Enough keystream bytes (in 64-byte blocks, counter incrementing from
-- `counterStart`) to cover `n` bytes.
keystream : (key : Vect 8 Bits32) -> (counterStart : Bits32) -> (nonce : Vect 3 Bits32) -> (n : Nat) -> List Bits8
keystream key counterStart nonce n =
  take n (go counterStart n)
  where
    go : Bits32 -> Nat -> List Bits8
    go _ Z = []
    go counter remaining =
      chachaBlock key counter nonce ++ go (counter + 1) (remaining `minus` 64)

||| Encrypts (or decrypts - XOR is its own inverse) `input` with ChaCha20.
||| `key` must be exactly 32 bytes, `nonce` exactly 12 bytes (RFC 8439's
||| format, as used by TLS 1.3 - not the original 8-byte-nonce Chacha20
||| variant). `counter` is normally 1 for TLS record protection (block 0
||| is reserved for the Poly1305 one-time key - see Crypto.ChaCha20Poly1305).
export
chacha20 : (key : List Bits8) -> (counter : Bits32) -> (nonce : List Bits8) -> (input : List Bits8) -> List Bits8
chacha20 keyBytes counter nonceBytes input =
  case (toVectKey (wordsLE keyBytes), toVectNonce (wordsLE nonceBytes)) of
       (Just key, Just nonce) => zipWith xor input (keystream key counter nonce (length input))
       _                      => []
  where
    toVectKey : List Bits32 -> Maybe (Vect 8 Bits32)
    toVectKey ws = case toVect 8 ws of
                        Just v  => Just v
                        Nothing => Nothing
    toVectNonce : List Bits32 -> Maybe (Vect 3 Bits32)
    toVectNonce ws = case toVect 3 ws of
                          Just v  => Just v
                          Nothing => Nothing
