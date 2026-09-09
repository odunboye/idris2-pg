module Crypto.SCRAM

-- SCRAM-SHA-256 (RFC 5802 / RFC 7677), Postgres's default authentication
-- method since v14. Built entirely on Crypto.SHA256 - no external crypto
-- library, consistent with this project's from-scratch approach elsewhere.
--
-- The client nonce uses contrib's System.Random (a standard, non-
-- cryptographic PRNG - Chez's built-in `random`), not a CSPRNG. That's
-- adequate here: per RFC 5802, the nonce only needs to be different each
-- time (anti-replay), not secret - none of SCRAM's security properties
-- depend on the client nonce being unpredictable, only on the password
-- itself and the server-contributed nonce extension.

import Crypto.SHA256
import Crypto.ChaCha20Poly1305
import Data.Bits
import Data.List
import Data.List1
import Data.String
import Derive.Prelude
import System.Random

%language ElabReflection
%default covering

strBytes : String -> List Bits8
strBytes s = map (cast . ord) (unpack s)

export
hmacSha256 : List Bits8 -> List Bits8 -> List Bits8
hmacSha256 key message =
  let blockSize = 64
      keyHashed = if length key > blockSize then sha256 key else key
      pad : List Bits8 -> List Bits8
      pad k = k ++ replicate (blockSize `minus` length k) 0
      key' = pad keyHashed
      ipadKey = map (\b => b `xor` 0x36) key'
      opadKey = map (\b => b `xor` 0x5c) key'
      inner = sha256 (ipadKey ++ message)
  in sha256 (opadKey ++ inner)

-- Single-block PBKDF2 (SCRAM-SHA-256's derived key length is always exactly
-- 32 bytes, one SHA-256 block, so there's no need for the general
-- multi-block T1||T2||... construction).
export
pbkdf2Sha256 : List Bits8 -> List Bits8 -> Int -> List Bits8
pbkdf2Sha256 password salt iterations =
  let u1 = hmacSha256 password (salt ++ [0, 0, 0, 1])
  in go (iterations - 1) u1 u1
  where
    go : Int -> List Bits8 -> List Bits8 -> List Bits8
    go n uPrev acc =
      if n <= 0
         then acc
         else let uNext = hmacSha256 password uPrev
              in go (n - 1) uNext (zipWith xor acc uNext)

b64Chars : List Char
b64Chars = unpack "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"

b64CharAt : Int -> Char
b64CharAt i = case drop (cast i) b64Chars of
     (c :: _) => c
     []       => '='

public export
base64Encode : List Bits8 -> String
base64Encode bytes = pack (go bytes)
  where
    go : List Bits8 -> List Char
    go (b1 :: b2 :: b3 :: rest) =
      let n : Int = (cast b1 `shiftL` 16) .|. (cast b2 `shiftL` 8) .|. cast b3
      in b64CharAt (n `shiftR` 18 .&. 0x3F)
           :: b64CharAt (n `shiftR` 12 .&. 0x3F)
           :: b64CharAt (n `shiftR` 6 .&. 0x3F)
           :: b64CharAt (n .&. 0x3F)
           :: go rest
    go [b1, b2] =
      let n : Int = (cast b1 `shiftL` 16) .|. (cast b2 `shiftL` 8)
      in [ b64CharAt (n `shiftR` 18 .&. 0x3F)
         , b64CharAt (n `shiftR` 12 .&. 0x3F)
         , b64CharAt (n `shiftR` 6 .&. 0x3F)
         , '='
         ]
    go [b1] =
      let n : Int = cast b1 `shiftL` 16
      in [ b64CharAt (n `shiftR` 18 .&. 0x3F)
         , b64CharAt (n `shiftR` 12 .&. 0x3F)
         , '=', '='
         ]
    go [] = []

b64Val : Char -> Maybe Int
b64Val c = go 0 b64Chars
  where
    go : Int -> List Char -> Maybe Int
    go _ [] = Nothing
    go i (x :: xs) = if x == c then Just i else go (i + 1) xs

public export
base64Decode : String -> Maybe (List Bits8)
base64Decode s = go (filter (/= '=') (unpack s))
  where
    combine4 : Int -> Int -> Int -> Int -> Nat -> List Bits8
    combine4 a b c d nOut =
      let n : Int = (a `shiftL` 18) .|. (b `shiftL` 12) .|. (c `shiftL` 6) .|. d
          allBytes : List Bits8
          allBytes = [ cast (n `shiftR` 16 .&. 0xFF), cast (n `shiftR` 8 .&. 0xFF), cast (n .&. 0xFF) ]
      in take nOut allBytes

    go : List Char -> Maybe (List Bits8)
    go [] = Just []
    go [c1, c2] = do
      a <- b64Val c1; b <- b64Val c2
      Just (combine4 a b 0 0 1)
    go [c1, c2, c3] = do
      a <- b64Val c1; b <- b64Val c2; c <- b64Val c3
      Just (combine4 a b c 0 2)
    go (c1 :: c2 :: c3 :: c4 :: rest) = do
      a <- b64Val c1; b <- b64Val c2; c <- b64Val c3; d <- b64Val c4
      more <- go rest
      Just (combine4 a b c d 3 ++ more)
    go _ = Nothing

||| A fresh client nonce: 18 random bytes, base64-encoded (24 characters,
||| no padding needed since 18 is a multiple of 3).
export
genClientNonce : IO String
genClientNonce = do
  bytes <- traverse (const randomByte) [the Int 1 .. 18]
  pure (base64Encode bytes)
  where
    randomByte : IO Bits8
    randomByte = cast <$> randomRIO {a = Int32} (0, 255)

public export
clientFirstMessageBare : String -> String
clientFirstMessageBare clientNonce = "n=,r=" ++ clientNonce

||| The full message sent as the SASLInitialResponse body: a GS2 header
||| (no channel binding, no authzid) followed by the bare message.
public export
clientFirstMessage : String -> String
clientFirstMessage clientNonce = "n,," ++ clientFirstMessageBare clientNonce

public export
record ServerFirstMessage where
  constructor MkServerFirstMessage
  nonce      : String
  salt       : List Bits8
  iterations : Int
%runElab derive "ServerFirstMessage" [Show, Eq]

-- Splits "r=<nonce>,s=<base64 salt>,i=<iterations>" (ignoring unknown
-- leading fields, per RFC 5802 extensibility) into its parts.
public export
parseServerFirstMessage : String -> Maybe ServerFirstMessage
parseServerFirstMessage s = go (forget (split (== ',') s)) Nothing Nothing Nothing
  where
    go : List String -> Maybe String -> Maybe (List Bits8) -> Maybe Int -> Maybe ServerFirstMessage
    go [] (Just n) (Just salt) (Just i) = Just (MkServerFirstMessage n salt i)
    go [] _ _ _ = Nothing
    go (field :: rest) mn ms mi =
      case unpack field of
           ('r' :: '=' :: n)     => go rest (Just (pack n)) ms mi
           ('s' :: '=' :: saltB64) => go rest mn (base64Decode (pack saltB64)) mi
           ('i' :: '=' :: iStr)  => go rest mn ms (parsePositive (pack iStr))
           _                     => go rest mn ms mi

public export
record ScramClientFinal where
  constructor MkScramClientFinal
  message                 : String
  expectedServerSignature : List Bits8

||| Computes the client-final-message and the ServerSignature we expect
||| back, given the password, the client's own nonce, the bare
||| client-first-message, the raw server-first-message text, and its
||| parsed form. Nothing if the server's combined nonce doesn't start with
||| the client's nonce (RFC 5802 requires checking this - an unrelated or
||| truncated nonce indicates a protocol error or a possible attack).
public export
computeClientFinal : (password : String) -> (clientNonce : String) -> (clientFirstBare : String)
                    -> (serverFirstRaw : String) -> ServerFirstMessage -> Maybe ScramClientFinal
computeClientFinal password clientNonce clientFirstBare serverFirstRaw sf =
  if not (isPrefixOf clientNonce (nonce sf))
     then Nothing
     else
       let saltedPassword = pbkdf2Sha256 (strBytes password) (salt sf) (iterations sf)
           clientKey = hmacSha256 saltedPassword (strBytes "Client Key")
           storedKey = sha256 clientKey
           clientFinalWithoutProof = "c=biws,r=" ++ nonce sf  -- biws = base64Encode(strBytes "n,,")
           authMessage = clientFirstBare ++ "," ++ serverFirstRaw ++ "," ++ clientFinalWithoutProof
           clientSignature = hmacSha256 storedKey (strBytes authMessage)
           clientProof = zipWith xor clientKey clientSignature
           finalMessage = clientFinalWithoutProof ++ ",p=" ++ base64Encode clientProof
           serverKey = hmacSha256 saltedPassword (strBytes "Server Key")
           serverSignature = hmacSha256 serverKey (strBytes authMessage)
       in Just (MkScramClientFinal finalMessage serverSignature)

||| Checks a server-final-message ("v=<base64 signature>") against the
||| ServerSignature computed in computeClientFinal - this is SCRAM's mutual
||| authentication step: it proves the server actually knows the stored
||| key material, not just that it echoed the right nonce.
public export
verifyServerFinal : String -> List Bits8 -> Bool
verifyServerFinal serverFinalRaw expectedSignature =
  case unpack serverFinalRaw of
       ('v' :: '=' :: rest) => case base64Decode (pack rest) of
                                     Just sig => constantTimeEq sig expectedSignature
                                     Nothing  => False
       _                    => False
