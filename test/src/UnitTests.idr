module UnitTests

import Data.List
import Data.Bits
import Data.PGTypes
import Helper
import Crypto.MD5
import Crypto.SHA256
import Crypto.SCRAM
import Crypto.Curve25519
import Crypto.P256
import Crypto.ChaCha20
import Data.Maybe
import Crypto.Poly1305
import Crypto.ChaCha20Poly1305
import Crypto.HKDF
import Network.TLSWire
import Network.TLSHandshake
import Data.PGValue
import Network.Timeout
import System

check : Show a => Eq a => String -> a -> a -> IO ()
check label expected actual =
  if expected == actual
     then putStrLn ("OK " ++ label)
     else putStrLn ("FAIL " ++ label ++ ": expected " ++ show expected ++ ", got " ++ show actual)

strBytes : String -> List Bits8
strBytes s = map (cast . ord) (unpack s)

hexToBytes : String -> List Bits8
hexToBytes s = go (unpack s)
  where
    hexVal : Char -> Int
    hexVal c = if c >= '0' && c <= '9' then cast (ord c - ord '0')
               else cast (ord c - ord 'a' + 10)
    go : List Char -> List Bits8
    go (a :: b :: rest) = cast (hexVal a * 16 + hexVal b) :: go rest
    go _                = []

-- n levels of nested arrays, e.g. nestedJSONArray 3 = "[[[1]]]".
nestedJSONArray : Nat -> String
nestedJSONArray n = pack (replicate n '[' ++ unpack "1" ++ replicate n ']')

-- n levels of nested Postgres array groups, e.g. nestedPGArray 3 = "{{{}}}".
nestedPGArray : Nat -> String
nestedPGArray n = pack (replicate n '{' ++ replicate n '}')

-- OID is irrelevant for text-format columns (checkBinaryOid never
-- inspects it), so it's a fixed placeholder here rather than a parameter.
mkTextRow : List (String, Maybe String) -> Row
mkTextRow cols = MkRow (map (\(n, v) => (n, FmtText, 0, map strBytes v)) cols)

mkBinaryRow : List (String, Int, Maybe (List Bits8)) -> Row
mkBinaryRow cols = MkRow (map (\(n, oid, v) => (n, FmtBinary, oid, v)) cols)

-- Checks that `bytes` is [tag] ++ encodeInt32 len ++ payload with
-- len == 4 + length payload (i.e. the frame is internally consistent),
-- then hands the payload to `checkPayload` for message-specific checks.
checkFrame : String -> Bits8 -> (List Bits8 -> IO ()) -> List Bits8 -> IO ()
checkFrame label expectedTag checkPayload bytes = case bytes of
     [] => putStrLn ("FAIL " ++ label ++ ": empty output")
     (tagByte :: rest) => case decodeInt32 rest of
          Left err => putStrLn ("FAIL " ++ label ++ " (bad length prefix): " ++ err)
          Right (len, payload) => do
            check (label ++ " tag byte") expectedTag tagByte
            check (label ++ " length field") (cast (length rest)) len
            checkPayload payload

main : IO ()
main = do
  -- MD5 (RFC 1321 official test vectors)
  check "md5 empty"    "d41d8cd98f00b204e9800998ecf8427e" (toHex (md5 (strBytes "")))
  check "md5 a"        "0cc175b9c0f1b6a831c399e269772661" (toHex (md5 (strBytes "a")))
  check "md5 abc"      "900150983cd24fb0d6963f7d28e17f72" (toHex (md5 (strBytes "abc")))
  check "md5 message digest" "f96b697d7cb7938d525a2f31aaf161d0" (toHex (md5 (strBytes "message digest")))
  check "md5 a-z"      "c3fcd3d76192e4007dfb496cca67e13b" (toHex (md5 (strBytes "abcdefghijklmnopqrstuvwxyz")))
  check "md5 alnum"    "d174ab98d277d9f5a5611c2c9f419d9f"
    (toHex (md5 (strBytes "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789")))
  check "md5 80 digits (multi-block)" "57edf4a22be3c955ac49da2e2107b67a"
    (toHex (md5 (strBytes "12345678901234567890123456789012345678901234567890123456789012345678901234567890")))
  check "md5 pangram"  "9e107d9d372bb6826bd81d3542a419d6"
    (toHex (md5 (strBytes "The quick brown fox jumps over the lazy dog")))

  -- SCRAM-SHA-256 building blocks (against Python hashlib/hmac/base64
  -- reference values)
  check "hmac-sha256" "f7bc83f430538424b13298e6aa6fb143ef4d59a14946175997479dbc2d1a3cd8"
    (toHex (hmacSha256 (strBytes "key") (strBytes "The quick brown fox jumps over the lazy dog")))
  check "pbkdf2-hmac-sha256 1 iter" "120fb6cffcf8b32c43e7225256c4f837a86548c92ccc35480805987cb70be17b"
    (toHex (pbkdf2Sha256 (strBytes "password") (strBytes "salt") 1))
  check "pbkdf2-hmac-sha256 4096 iters" "c5e478d59288c841aa530db6845c4c8d962893a001ce4e11a4963873aa98134a"
    (toHex (pbkdf2Sha256 (strBytes "password") (strBytes "salt") 4096))
  check "base64Encode empty" "" (base64Encode [])
  check "base64Encode foobar" "Zm9vYmFy" (base64Encode (strBytes "foobar"))
  check "base64Encode padding 1" "Zm8=" (base64Encode (strBytes "fo"))
  check "base64Encode padding 2" "Zg==" (base64Encode (strBytes "f"))
  check "base64Decode foobar" (Just (strBytes "foobar")) (base64Decode "Zm9vYmFy")
  check "base64 roundtrip" (Just [0 .. 17]) (base64Decode (base64Encode [0 .. 17]))
  check "parseServerFirstMessage"
    (Just (MkServerFirstMessage "abc123" (strBytes "salty") 4096))
    (parseServerFirstMessage ("r=abc123,s=" ++ base64Encode (strBytes "salty") ++ ",i=4096"))
  check "parseServerFirstMessage malformed" Nothing (parseServerFirstMessage "not,a,valid,message")

  -- encode: client-to-server messages
  checkFrame "QueryMsg" 0x51
    (\payload => case decodeCString payload of
         Right (s, []) => check "QueryMsg body" "SELECT 1" s
         other => putStrLn ("FAIL QueryMsg payload: " ++ show other))
    (encode (QueryMsg (MkQuery "SELECT 1")))

  checkFrame "PasswordMessage" 0x70
    (\payload => case decodeCString payload of
         Right (s, []) => check "PasswordMessage body" "md5abc123" s
         other => putStrLn ("FAIL PasswordMessage payload: " ++ show other))
    (encode (PasswordMessage "md5abc123"))

  checkFrame "Parse" 0x50
    (\payload => case decodeCString payload of
         Right ("", afterName) => case decodeCString afterName of
              Right ("SELECT $1", afterQuery) => case decodeInt16 afterQuery of
                   Right (1, afterCount) => case decodeInt32 afterCount of
                        Right (23, []) => putStrLn "OK Parse payload"
                        other => putStrLn ("FAIL Parse param OID: " ++ show other)
                   other => putStrLn ("FAIL Parse param count: " ++ show other)
              other => putStrLn ("FAIL Parse query text: " ++ show other)
         other => putStrLn ("FAIL Parse stmt name: " ++ show other))
    (encode (Parse "" "SELECT $1" [23]))

  checkFrame "Bind" 0x42
    (\payload => case decodeCString payload of
         Right ("", afterPortal) => case decodeCString afterPortal of
              Right ("", afterStmt) => case decodeInt16 afterStmt of
                   Right (0, afterFmtCount) => case decodeInt16 afterFmtCount of
                        Right (2, afterParamCount) => case decodeInt32 afterParamCount of
                             Right (5, afterLen1) =>
                               let (valBytes, afterVal1) = splitAt 5 afterLen1
                               in case decodeInt32 afterVal1 of
                                       Right (-1, afterLen2) => do
                                         check "Bind param1 value" (strBytes "hello") valBytes
                                         check "Bind trailing result-format count" (encodeInt16 0) afterLen2
                                       other => putStrLn ("FAIL Bind NULL marker: " ++ show other)
                             other => putStrLn ("FAIL Bind param 1 length: " ++ show other)
                        other => putStrLn ("FAIL Bind param count: " ++ show other)
                   other => putStrLn ("FAIL Bind format count: " ++ show other)
              other => putStrLn ("FAIL Bind stmt name: " ++ show other)
         other => putStrLn ("FAIL Bind portal name: " ++ show other))
    (encode (Bind "" "" [Just (strBytes "hello"), Nothing] False))

  checkFrame "Bind with binary results" 0x42
    (\payload => case decodeCString payload of
         Right ("", afterPortal) => case decodeCString afterPortal of
              Right ("", afterStmt) => case decodeInt16 afterStmt of
                   Right (0, afterFmtCount) => case decodeInt16 afterFmtCount of
                        Right (0, afterParamCount) => case decodeInt16 afterParamCount of
                             Right (1, afterResultCount) => case decodeInt16 afterResultCount of
                                  Right (1, []) => putStrLn "OK Bind binary-results format section"
                                  other => putStrLn ("FAIL Bind binary result format code: " ++ show other)
                             other => putStrLn ("FAIL Bind result format count: " ++ show other)
                        other => putStrLn ("FAIL Bind param count: " ++ show other)
                   other => putStrLn ("FAIL Bind format count: " ++ show other)
              other => putStrLn ("FAIL Bind stmt name: " ++ show other)
         other => putStrLn ("FAIL Bind portal name: " ++ show other))
    (encode (Bind "" "" [] True))

  check "Sync bytes" [0x53, 0, 0, 0, 4] (encode Sync)
  check "Terminate bytes" [0x58, 0, 0, 0, 4] (encode Terminate)
  check "CancelRequest bytes"
    ([0,0,0,16] ++ [0x04,0xd2,0x16,0x2e] ++ [0,0,0,42] ++ [0,0,0,99])
    (encode (CancelRequest 42 99))

  checkFrame "CopyData (client-sent)" 0x64
    (\payload => check "CopyData payload" (strBytes "1\thello\n") payload)
    (encode (CopyData (strBytes "1\thello\n")))
  check "CopyDone bytes" [0x63, 0, 0, 0, 4] (encode CopyDone)
  checkFrame "CopyFail" 0x66
    (\payload => case decodeCString payload of
         Right ("oops", []) => putStrLn "OK CopyFail payload"
         other => putStrLn ("FAIL CopyFail payload: " ++ show other))
    (encode (CopyFail "oops"))

  -- decode: server-to-client messages
  check "decode AuthenticationOk" (Right (AuthenticationMsg AuthOk))
    (decode (MkFrameBytes [toByte AuthenticationTag] (encodeInt32 8) (encodeInt32 0)))

  check "decode ReadyForQuery Idle" (Right (ReadyForQueryMsg Idle))
    (decode (MkFrameBytes [toByte ReadyForQueryTag] (encodeInt32 5) [0x49]))

  check "decode CommandComplete" (Right (CommandCompleteMsg "INSERT 0 1"))
    (decode (MkFrameBytes [toByte CommandCompleteTag] (encodeInt32 15) (encodeCString "INSERT 0 1")))

  let paramDescPayload = encodeInt16 1 ++ encodeInt32 23
  check "decode ParameterDescription" (Right (ParameterDescriptionMsg [23]))
    (decode (MkFrameBytes [toByte ParameterDescriptionTag] (encodeInt32 (cast (4 + length paramDescPayload))) paramDescPayload))

  let notifyPayload = encodeInt32 1234 ++ encodeCString "mychannel" ++ encodeCString "payload text"
  check "decode NotificationResponse"
    (Right (NotificationMsg (MkNotification 1234 "mychannel" "payload text")))
    (decode (MkFrameBytes [toByte NotificationResponseTag] (encodeInt32 (cast (4 + length notifyPayload))) notifyPayload))

  let errorPayload = strBytes "S" ++ encodeCString "ERROR"
                       ++ strBytes "C" ++ encodeCString "42601"
                       ++ strBytes "M" ++ encodeCString "syntax error"
                       ++ [0]
  case decode (MkFrameBytes [toByte ErrorResponseTag] (encodeInt32 (cast (4 + length errorPayload))) errorPayload) of
       Right (ErrorMsg e) => do
         check "decode ErrorResponse severity" (Just "ERROR") (severity e)
         check "decode ErrorResponse code" (Just "42601") (code e)
         check "decode ErrorResponse message" "syntax error" (message e)
       other => putStrLn ("FAIL decode ErrorResponse: " ++ show other)

  check "decode CopyData (server-sent)" (Right (CopyData (strBytes "1\thello\n")))
    (decode (MkFrameBytes [toByte CopyDataTag] (encodeInt32 12) (strBytes "1\thello\n")))
  check "decode CopyDone" (Right CopyDone)
    (decode (MkFrameBytes [toByte CopyDoneTag] (encodeInt32 4) []))
  let copyOutPayload = [0] ++ encodeInt16 2 ++ encodeInt16 0 ++ encodeInt16 0
  check "decode CopyOutResponse" (Right (CopyOutResponseMsg 0 [0, 0]))
    (decode (MkFrameBytes [toByte CopyOutResponseTag] (encodeInt32 (cast (4 + length copyOutPayload))) copyOutPayload))
  let copyInPayload = [0] ++ encodeInt16 1 ++ encodeInt16 0
  check "decode CopyInResponse" (Right (CopyInResponseMsg 0 [0]))
    (decode (MkFrameBytes [toByte CopyInResponseTag] (encodeInt32 (cast (4 + length copyInPayload))) copyInPayload))

  -- Data.PGValue parsers
  check "parsePGArray simple" (Right [Just "1", Just "2", Just "3"]) (parsePGArray "{1,2,3}")
  check "parsePGArray empty" (Right []) (parsePGArray "{}")
  check "parsePGArray with null" (Right [Just "a", Nothing, Just "b"]) (parsePGArray "{a,NULL,b}")
  check "parsePGArray quoted comma" (Right [Just "a,b", Just "c"]) (parsePGArray "{\"a,b\",c}")
  check "parsePGArray quoted escape" (Right [Just "a\"b"]) (parsePGArray "{\"a\\\"b\"}")
  check "parsePGArray quoted NULL literal" (Right [Just "NULL"]) (parsePGArray "{\"NULL\"}")
  check "parsePGArray bad format" (Left "array value must start with '{'") (parsePGArray "1,2,3")

  -- multi-dimensional arrays (PGArrayValue / getArray2D)
  check "parsePGArrayValue 2D"
    (Right (PGGroup [PGGroup [PGLeaf (Just "1"), PGLeaf (Just "2")], PGGroup [PGLeaf (Just "3"), PGLeaf (Just "4")]]))
    (parsePGArrayValue "{{1,2},{3,4}}")
  check "parsePGArrayValue 2D with null and quoted comma"
    (Right (PGGroup [PGGroup [PGLeaf Nothing, PGLeaf (Just "a,b")]]))
    (parsePGArrayValue "{{NULL,\"a,b\"}}")
  check "parsePGArrayValue 3D"
    (Right (PGGroup [PGGroup [PGGroup [PGLeaf (Just "1")], PGGroup [PGLeaf (Just "2")]]]))
    (parsePGArrayValue "{{{1},{2}}}")
  check "parsePGArray on a 2D value reports a clear error" True
    (isLeft (parsePGArray "{{1,2},{3,4}}"))
  check "getArray2D" (Right [[Just "1", Just "2"], [Just "3", Just "4"]])
    (getArray2D (mkTextRow [("m", Just "{{1,2},{3,4}}")]) "m")
  check "getArray2D on a 1D value reports a clear error" True
    (isLeft (getArray2D (mkTextRow [("m", Just "{1,2}")]) "m"))

  check "getInt ok" (Right 42) (getInt (mkTextRow [("n", Just "42")]) "n")
  check "getInt bad" True (isLeft (getInt (mkTextRow [("n", Just "abc")]) "n"))
  check "getInt null" True (isLeft (getInt (mkTextRow [("n", Nothing)]) "n"))
  check "getBool t" (Right True) (getBool (mkTextRow [("b", Just "t")]) "b")
  check "getBool f" (Right False) (getBool (mkTextRow [("b", Just "f")]) "b")
  check "getDouble ok" (Right 3.5) (getDouble (mkTextRow [("d", Just "3.5")]) "d")

  -- binary-format value decoding (Data.PGBinary, via getInt/getBool/getDouble)
  -- OIDs: bool=16, int8=20, int2=21, int4=23, text=25, float4=700, float8=701
  check "getInt binary int2" (Right 300) (getInt (mkBinaryRow [("n", 21, Just (encodeInt16 300))]) "n")
  check "getInt binary int4" (Right 70000) (getInt (mkBinaryRow [("n", 23, Just (encodeInt32 70000))]) "n")
  check "getInt binary int8" (Right 300) (getInt (mkBinaryRow [("n", 20, Just [0, 0, 0, 0, 0, 0, 1, 0x2c])]) "n")
  check "getInteger binary int8 widens" (Right 300) (getInteger (mkBinaryRow [("n", 20, Just [0, 0, 0, 0, 0, 0, 1, 0x2c])]) "n")
  check "getBool binary true" (Right True) (getBool (mkBinaryRow [("b", 16, Just [1])]) "b")
  check "getBool binary false" (Right False) (getBool (mkBinaryRow [("b", 16, Just [0])]) "b")
  check "getDouble binary float4 1.0" (Right 1.0) (getDouble (mkBinaryRow [("d", 700, Just [0x3f, 0x80, 0x00, 0x00])]) "d")
  check "getDouble binary float8 1.0" (Right 1.0)
    (getDouble (mkBinaryRow [("d", 701, Just [0x3f, 0xf0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00])]) "d")
  check "getInt binary wrong width reports a clear error" True
    (isLeft (getInt (mkBinaryRow [("n", 23, Just [1, 2, 3])]) "n"))
  check "getInt binary rejects a mismatched type OID" True
    (isLeft (getInt (mkBinaryRow [("n", 700, Just [0x3f, 0x80, 0x00, 0x00])]) "n"))
  check "columnByName works for binary text-like column" (Just (Just "hi"))
    (columnByName (mkBinaryRow [("s", 25, Just (strBytes "hi"))]) "s")

  -- UTF-8 (Helper.stringToBytes/bytesToString), not the Latin-1-style byte
  -- mapping this used to do - accented letters, non-Latin scripts, and an
  -- emoji all survive a round trip.
  let utf8Text = "café — naïve façade 日本語 🎉"
  check "stringToBytes/bytesToString round-trips non-ASCII text" utf8Text
    (bytesToString (stringToBytes utf8Text))
  check "getText round-trips non-ASCII text through a Row" (Right utf8Text)
    (getText (MkRow [("s", FmtText, 0, Just (stringToBytes utf8Text))]) "s")
  check "getInteger big" (Right 123456789012345678901234567890)
    (getInteger (mkTextRow [("n", Just "123456789012345678901234567890")]) "n")
  check "getDate ok" (Right (MkPGDate 2024 3 7)) (getDate (mkTextRow [("d", Just "2024-03-07")]) "d")
  check "getTimestamp ok" (Right (MkPGTimestamp (MkPGDate 2024 3 7) 13 45 30))
    (getTimestamp (mkTextRow [("ts", Just "2024-03-07 13:45:30")]) "ts")
  check "getTimestamp with fraction" (Right (MkPGTimestamp (MkPGDate 2024 3 7) 13 45 30))
    (getTimestamp (mkTextRow [("ts", Just "2024-03-07 13:45:30.123456")]) "ts")

  -- JSON (Data.PGJson, via getJSON)
  check "parseJSON null" (Right JNull) (parseJSON "null")
  check "parseJSON number" (Right (JNumber 42.0)) (parseJSON "42")
  check "parseJSON string with escapes" (Right (JString "a\"b\\c\nd")) (parseJSON "\"a\\\"b\\\\c\\nd\"")
  check "parseJSON string with unicode escape" (Right (JString "caf\233")) (parseJSON "\"caf\\u00e9\"")
  check "parseJSON array" (Right (JArray [JNumber 1.0, JNumber 2.0])) (parseJSON "[1,2]")
  check "parseJSON nested object" (Right (JObject [("x", JArray [JObject [("y", JNull)]])]))
    (parseJSON "{\"x\":[{\"y\":null}]}")
  check "parseJSON whitespace tolerant" (Right (JObject [("a", JNumber 1.0)])) (parseJSON " { \"a\" : 1 } ")
  check "parseJSON trailing content rejected" True (isLeft (parseJSON "1 2"))
  check "parseJSON bad literal rejected" True (isLeft (parseJSON "nul"))
  check "getJSON" (Right (JObject [("a", JNumber 1.0)])) (getJSON (mkTextRow [("j", Just "{\"a\":1}")]) "j")

  -- parseJSON's depth budget: moderate nesting still parses, but a server
  -- couldn't use deeply nested JSON to exhaust the call stack (each level
  -- is one array-array recursion; see maxJSONDepth in Data.PGJson).
  check "parseJSON tolerates moderately nested arrays" True
    (not (isLeft (parseJSON (nestedJSONArray 50))))
  check "parseJSON rejects excessively nested arrays" True
    (isLeft (parseJSON (nestedJSONArray 500)))

  -- parsePGArrayValue's depth budget: same idea for Postgres array text
  -- (see maxArrayDepth in Data.PGValue).
  check "parsePGArrayValue tolerates moderately nested groups" True
    (not (isLeft (parsePGArrayValue (nestedPGArray 50))))
  check "parsePGArrayValue rejects excessively nested groups" True
    (isLeft (parsePGArrayValue (nestedPGArray 500)))

  -- Helper.validateFrameLength: the sanity check on a server-declared
  -- message length, guarding against a huge or negative-after-subtracting
  -- payload size driving an unbounded/desynced read (see Helper.idr).
  check "validateFrameLength accepts a normal length" (Right 6) (validateFrameLength 10)
  check "validateFrameLength rejects a length smaller than the prefix itself" True
    (isLeft (validateFrameLength 3))
  check "validateFrameLength rejects a payload over the size cap" True
    (isLeft (validateFrameLength (maxFrameBodySize + 5)))

  -- Network.Timeout: cooperative, thread-based withTimeout
  fastResult <- withTimeout 200 (pure 42)
  check "withTimeout returns the result when the action finishes in time" (Just 42) fastResult

  slowResult <- withTimeout 30 (usleep 300000 *> pure 42)
  check "withTimeout returns Nothing when the action doesn't finish in time" Nothing slowResult

  -- Crypto.Curve25519 (X25519), against an independently-generated
  -- reference keypair/shared-secret (Python's `cryptography` library).
  let aPriv = hexToBytes "688e97675f7f17372b550e3d50d9af6411ff9ee2b0cb593f6a150e2d15906869"
  let bPriv = hexToBytes "00d31c383ff407c5fb7edd098d04163c52aa53445d50edf49bbc140150f9de7e"
  let aPub  = "4dddffba9a7e257049f70257d01146840c11ff05a6ca7a84ba1fb7053fd0f224"
  let bPub  = "f65fddc114cff1c1dd63df8a61c88d7f3c4654da564605bb9d491d09124e2d68"
  let shared = "c3087a54de22e311b6744865dbfd631f424a89ab7ae6fde3ddae9b6f3746e30e"
  check "x25519PublicKey derives Alice's public key" aPub (toHex (x25519PublicKey aPriv))
  check "x25519PublicKey derives Bob's public key" bPub (toHex (x25519PublicKey bPriv))
  check "x25519 shared secret (Alice's view)" shared (toHex (x25519 aPriv (hexToBytes bPub)))
  check "x25519 shared secret (Bob's view)" shared (toHex (x25519 bPriv (hexToBytes aPub)))

  -- Crypto.P256: a genuine peer point (from p256PublicKey) is accepted,
  -- but an arbitrary/off-curve "point" - the same shape a compromised or
  -- buggy peer could hand this client - is rejected before it ever
  -- reaches scalar multiplication.
  let p256PrivA = replicate 31 0 ++ [7]
  let p256PrivB = replicate 31 0 ++ [9]
  check "p256SharedSecret accepts a genuine on-curve peer point" True
    (isJust (p256SharedSecret p256PrivA (p256PublicKey p256PrivB)))
  let offCurvePoint = [0x04] ++ replicate 31 0 ++ [1] ++ replicate 31 0 ++ [1]  -- (1, 1); not on the curve
  check "p256SharedSecret rejects an off-curve peer point" Nothing
    (p256SharedSecret p256PrivA offCurvePoint)

  -- Crypto.ChaCha20, against Python cryptography-generated reference
  -- keystreams (a single-block and a multi-block, non-64-byte-aligned case).
  let ccKey1 = hexToBytes "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"
  let ccNonce1 = hexToBytes "000000090000004a00000000"
  let ccExpected1 = "10f1e7e4d13b5915500fdd1fa32071c4c7d1f4c733c068030422aa9ac3d46c4ed2826446079faa0914c2d705d98b02a2b5129cd1de164eb9cbd083e8a2503c4e"
  check "chacha20 block keystream, counter=1" ccExpected1 (toHex (chacha20 ccKey1 1 ccNonce1 (replicate 64 0)))

  let ccKey2 = hexToBytes "19100317fa185880b21df4527bd81ad27a7ca1f83f7ac360198384d7bee624e0"
  let ccNonce2 = hexToBytes "99b88da14222e026f14b6b1a"
  let ccExpected2 = "ed4d3f4da99f94533e4820e2be60171428360c4141e55ab27a89b59a385c12d5a270ee4b1c745a632bc9c79fbdb9b9aa48fb4d9386aa2b0de911ebc55fee459b0aac977bd983d2d135952a4e9f7bf2d52221acf2984cc33b0b0289ba75baa65e1de96846f6a9cdd5eb753c0d2bb5e4a3653ce403b763a4f859a212319198d1d9c03891bc44e78ff2fb3123f7b67cf8243005060d25627009049ed46f1dbdf71c5e872d46588fd22e9b95a2b37798ba1075cb4613b7e6d7fc45e6d9a8e81d30b69576311e7eef3eb9"
  check "chacha20 multi-block keystream, counter=5, 200 bytes" ccExpected2
    (toHex (chacha20 ccKey2 5 ccNonce2 (replicate 200 0)))

  let ccPlain = strBytes "the quick brown fox jumps over the lazy dog, 1234567890!"
  let ccCipher = chacha20 ccKey1 1 ccNonce1 ccPlain
  check "chacha20 round-trip (decrypt undoes encrypt)" True (chacha20 ccKey1 1 ccNonce1 ccCipher == ccPlain)

  -- Crypto.Poly1305, against Python cryptography-generated reference tags.
  let pKey1 = hexToBytes "741f01e2d81caf7ccd490abda24222212ec4842a607373b7cf998e456a8510bc"
  let pMsg1 = hexToBytes "43727970746f6772617068696320466f72756d2052657365617263682047726f7570"
  check "poly1305 tag" "debd358adca479f7f4c06346171ade21" (toHex (poly1305 pKey1 pMsg1))

  let pKey2 = hexToBytes "6f62bf65ac2329171d7528dfb01314b50c0930947d51a394634576f905873ed2"
  let pMsg2 = hexToBytes "097d3c6ed1644b19cc92d09907686ca1ffe92a49e1f48e89f0bca46ceaf5acdd13ac91624a5ccbbe96d5ad82f0343345d26a66db2109fb4c55829585cf810ecb658e1089f0a667c97377efd419c0970bc0a410fb6bcdb0aed4e749b25953783ddd"
  check "poly1305 tag on a non-16-byte-aligned message" "9ae4156b5a5f201f80a2fdc95928a8e5" (toHex (poly1305 pKey2 pMsg2))

  let pKey3 = hexToBytes "d86877c4b05d71ca0631f4a50b39f0161d8dc779c1aff63d15ef1e14bb467eb7"
  check "poly1305 tag on an empty message" "1d8dc779c1aff63d15ef1e14bb467eb7" (toHex (poly1305 pKey3 []))

  -- Crypto.ChaCha20Poly1305, against Python cryptography-generated
  -- reference ciphertext+tag, plus a decrypt round-trip and a
  -- tamper-detection check that isn't derivable from Python alone.
  let aeadKey1 = hexToBytes "c320ed24b7032d60c31606f4cab0d2fea47ab083067f37af95cc5c84f0ba4e56"
  let aeadNonce1 = hexToBytes "7658fd7f015d070d79051c22"
  let aeadAad1 = hexToBytes "6164646974696f6e616c206461746120313233"
  let aeadPt1 = hexToBytes "4c616469657320616e642047656e746c656d656e206f662074686520636c617373206f66202739393a204966204920636f756c64206f6666657220796f75206f6e6c79206f6e652074697020666f7220746865206675747572652c2073756e73637265656e20776f756c642062652069742e"
  let (aeadCt1, aeadTag1) = encrypt aeadKey1 aeadNonce1 aeadAad1 aeadPt1
  check "chacha20poly1305 ciphertext"
    "c8f7ce349c664f3d59018c724ebbea74183c3755d2bc4c400c7123b893171ef7ea09073f7f5a17c8c6c83d2afa5112dd7526039106c42941b1cedf5d17f2f592d7482248266a5ad277211d9ca9b7ad9a0963e54dffea1098178cfe5970c646f88c0b66cc04143c2f75d4e3f6e4e2bdda3217"
    (toHex aeadCt1)
  check "chacha20poly1305 tag" "ff2a6d9593f8470a355c9df8d16fcd5c" (toHex aeadTag1)
  check "chacha20poly1305 decrypt round-trip" (Just aeadPt1) (decrypt aeadKey1 aeadNonce1 aeadAad1 aeadCt1 aeadTag1)
  case aeadCt1 of
       (b0 :: rest) =>
         check "chacha20poly1305 rejects a tampered ciphertext" Nothing
           (decrypt aeadKey1 aeadNonce1 aeadAad1 ((b0 `xor` 1) :: rest) aeadTag1)
       [] => putStrLn "FAIL chacha20poly1305 tamper check: ciphertext was unexpectedly empty"

  -- Crypto.HKDF, against Python cryptography-generated reference vectors
  -- (generic HKDF-Extract/Expand, plus HKDF-Expand-Label checked against
  -- an independent Python reimplementation of RFC 8446's HkdfLabel struct).
  let hkdfSalt1 = hexToBytes "7670cb4cef0c526cdab53a08b1"
  let hkdfIkm1 = hexToBytes "e9ae6fed814022410fd3a8f59461228535e3117b57a6"
  let hkdfInfo1 = hexToBytes "cb9ac402be3f0e9a00cc"
  let hkdfPrk1 = hkdfExtract hkdfSalt1 hkdfIkm1
  check "hkdfExtract" "e03c04d0f1d9b10fd73947599a672615c575ee9a56428071ce475ebbd2f70e42" (toHex hkdfPrk1)
  check "hkdfExpand" "19b58ee029db6699a82b4094a22378b93e45e4676f5790749894427ba4a4ed9576e6c955a751a8e0610f"
    (toHex (hkdfExpand hkdfPrk1 hkdfInfo1 42))

  let hkdfSalt2 = hexToBytes "4930cffed77e49f786d9ce4d6b025e67"
  let hkdfIkm2 = hexToBytes "234980cf8b465c16a1423b4ab674a788369f368396330925b47cf30b36df4759"
  let hkdfPrk2 = hkdfExtract hkdfSalt2 hkdfIkm2
  check "hkdfExpand across multiple HMAC blocks (100 bytes, empty info)"
    "e03279c7e6536ab41ceee881ca9cfcdfbb04a927a234054064e9a2cf85b566ea23fe7aa350869e6db3f6b976c53f65ad047648563651ef914d80595740fd1c5a4e162d94c4c052f99b1fd4c9d0e66a659a1202a64b252c3dc60eb436c9c4dbbeb309a0a4"
    (toHex (hkdfExpand hkdfPrk2 [] 100))

  let hkdfSecret3 = hexToBytes "bef2ab5766dbb510bf50c2d39a5475d1ed9e28de27f78b261ccabaf7031551fe"
  let hkdfContext3 = hexToBytes "d1f71bbd8250b0947cfcd0d730980939911ac0706117dc54895c4077c0a4ee7f"
  check "hkdfExpandLabel (RFC 8446 HkdfLabel struct)" "94843d3f863bd550652c2a3cdfc82925c503be2e618cd71832f48a63cc83de86"
    (toHex (hkdfExpandLabel hkdfSecret3 "c hs traffic" hkdfContext3 32))

  -- Crypto.Curve25519 + Crypto.SHA256 + Crypto.HKDF, wired together as
  -- TLS 1.3's key schedule (RFC 8446 section 7.1), against RFC 8448's
  -- official "Simple 1-RTT Handshake" example - the exact ClientHello/
  -- ServerHello bytes, ephemeral X25519 keys, and every intermediate
  -- secret IETF published, all in one chain: the ECDHE shared secret
  -- feeds the early secret, which derives the handshake secret (salted by
  -- a "derived" secret over the empty-string hash), which derives the
  -- client/server handshake traffic secrets and (via another "derived")
  -- the master secret, which derives both application traffic secrets.
  -- A bug anywhere in this chain - X25519, HKDF-Extract, HKDF-Expand-
  -- Label's struct encoding, or the label/context wiring between steps -
  -- would show up as a mismatch somewhere in this list.
  let tls_client_priv = hexToBytes "49af42ba7f7994852d713ef2784bcbcaa7911de26adc5642cb634540e7ea5005"
  let tls_client_pub = hexToBytes "99381de560e4bd43d23d8e435a7dbafeb3c06e51c13cae4d5413691e529aaf2c"
  let tls_server_priv = hexToBytes "b1580eeadf6dd589b8ef4f2d5652578cc810e9980191ec8d058308cea216a21e"
  let tls_server_pub = hexToBytes "c9828876112095fe66762bdbf7c672e156d6cc253b833df1dd69b1b04e751f0f"
  let tls_client_hello = hexToBytes "010000c00303cb34ecb1e78163ba1c38c6dacb196a6dffa21a8d9912ec18a2ef6283024dece7000006130113031302010000910000000b0009000006736572766572ff01000100000a00140012001d0017001800190100010101020103010400230000003300260024001d002099381de560e4bd43d23d8e435a7dbafeb3c06e51c13cae4d5413691e529aaf2c002b0003020304000d0020001e040305030603020308040805080604010501060102010402050206020202002d00020101001c00024001"
  let tls_server_hello = hexToBytes "020000560303a6af06a4121860dc5e6e60249cd34c95930c8ac5cb1434dac155772ed3e2692800130100002e00330024001d0020c9828876112095fe66762bdbf7c672e156d6cc253b833df1dd69b1b04e751f0f002b00020304"
  let tls_early_secret = hexToBytes "33ad0a1c607ec03b09e6cd9893680ce210adf300aa1f2660e1b22e10f170f92a"
  let tls_handshake_ikm = hexToBytes "8bd4054fb55b9d63fdfbacf9f04b9f0d35e6d63f537563efd46272900f89492d"
  let tls_handshake_secret = hexToBytes "1dc826e93606aa6fdc0aadc12f741b01046aa6b99f691ed221a9f0ca043fbeac"
  let tls_c_hs_traffic = hexToBytes "b3eddb126e067f35a780b3abf45e2d8f3b1a950738f52e9600746a0e27a55a21"
  let tls_s_hs_traffic = hexToBytes "b67b7d690cc16c4e75e54213cb2d37b4e9c912bcded9105d42befd59d391ad38"
  let tls_master_secret = hexToBytes "18df06843d13a08bf2a449844c5f8a478001bc4d4c627984d5a41da8d0402919"
  let tls_c_ap_traffic = hexToBytes "9e40646ce79a7f9dc05af8889bce6552875afa0b06df0087f792ebb7c17504a5"
  let tls_s_ap_traffic = hexToBytes "a11af9f05531f856ad47116b45a950328204b4f44bfb6b3a4b4f1f3fcb631643"
  let tls_hash_ch_sh = hexToBytes "860c06edc07858ee8e78f0e7428c58edd6b43f2ca3e6e95f02ed063cf0e1cad8"
  let tls_hash_empty = hexToBytes "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
  let tls_server_finished = hexToBytes "9b9b141d906337fbd2cbdce71df4deda4ab42c309572cb7fffee5454b78f0718"
  let tls_client_finished = hexToBytes "a8ec436d677634ae525ac1fcebe11a039ec17694fac6e98527b642f2edd5ce61"
  let tls_hash_full = hexToBytes "9608102a0f1ccc6db6250b7b7e417b1a000eaada3daae4777a7686c9ff83df13"
  check "TLS 1.3: client-computed ECDHE shared secret" (toHex tls_handshake_ikm) (toHex (x25519 tls_client_priv tls_server_pub))
  check "TLS 1.3: server-computed ECDHE shared secret" (toHex tls_handshake_ikm) (toHex (x25519 tls_server_priv tls_client_pub))
  check "TLS 1.3: transcript hash (ClientHello||ServerHello)" (toHex tls_hash_ch_sh) (toHex (sha256 (tls_client_hello ++ tls_server_hello)))
  check "TLS 1.3: sha256 of the empty string" (toHex tls_hash_empty) (toHex (sha256 []))

  let tls_zero32 = replicate 32 0
  let tls_earlySecret = hkdfExtract tls_zero32 tls_zero32
  check "TLS 1.3: early secret" (toHex tls_early_secret) (toHex tls_earlySecret)

  let tls_derived1 = deriveSecret tls_earlySecret "derived" tls_hash_empty
  let tls_handshakeSecret = hkdfExtract tls_derived1 tls_handshake_ikm
  check "TLS 1.3: handshake secret" (toHex tls_handshake_secret) (toHex tls_handshakeSecret)
  check "TLS 1.3: client handshake traffic secret" (toHex tls_c_hs_traffic)
    (toHex (deriveSecret tls_handshakeSecret "c hs traffic" tls_hash_ch_sh))
  check "TLS 1.3: server handshake traffic secret" (toHex tls_s_hs_traffic)
    (toHex (deriveSecret tls_handshakeSecret "s hs traffic" tls_hash_ch_sh))

  let tls_derived2 = deriveSecret tls_handshakeSecret "derived" tls_hash_empty
  let tls_masterSecret = hkdfExtract tls_derived2 tls_zero32
  check "TLS 1.3: master secret" (toHex tls_master_secret) (toHex tls_masterSecret)
  check "TLS 1.3: client application traffic secret" (toHex tls_c_ap_traffic)
    (toHex (deriveSecret tls_masterSecret "c ap traffic" tls_hash_full))
  check "TLS 1.3: server application traffic secret" (toHex tls_s_ap_traffic)
    (toHex (deriveSecret tls_masterSecret "s ap traffic" tls_hash_full))

  -- Network.TLSHandshake, against a real ServerHello captured from a live
  -- handshake against an unmodified `postgres:16` server (parsing a
  -- message this client didn't construct itself is the meaningful check;
  -- an encode/decode round-trip of our own output can't catch a decoder
  -- that's wrong in the same way its matching encoder is). P-256, not
  -- x25519 - see Network.TLSHandshake's module comment for why.
  let liveServerHelloBody = hexToBytes "0303764c646908d0139fc63508036f695d4de2210ab970bcd6cdaaf55511c39be97a00130300004f002b0002030400330045001700410463124783f609001eb9d142e8043a7d511cdf3f334417e3fc2731fe8c3dbab975a2f233c540db152c0ef7824e56b37de4ee1f139fffd5cac1a38f33e7f7011b36"
  case parseServerHello liveServerHelloBody of
       Nothing => putStrLn "FAIL parseServerHello: returned Nothing on a real ServerHello"
       Just sh => do
         check "parseServerHello: serverRandom" "764c646908d0139fc63508036f695d4de2210ab970bcd6cdaaf55511c39be97a" (toHex (serverRandom sh))
         check "parseServerHello: cipherSuite" 0x1303 (cipherSuite sh)
         check "parseServerHello: serverPublicKey" "0463124783f609001eb9d142e8043a7d511cdf3f334417e3fc2731fe8c3dbab975a2f233c540db152c0ef7824e56b37de4ee1f139fffd5cac1a38f33e7f7011b36" (toHex (serverPublicKey sh))

  let liveFullServerHello = hexToBytes "020000770303764c646908d0139fc63508036f695d4de2210ab970bcd6cdaaf55511c39be97a00130300004f002b0002030400330045001700410463124783f609001eb9d142e8043a7d511cdf3f334417e3fc2731fe8c3dbab975a2f233c540db152c0ef7824e56b37de4ee1f139fffd5cac1a38f33e7f7011b36"
  case decodeHandshakeMessage liveFullServerHello of
       Nothing => putStrLn "FAIL decodeHandshakeMessage: returned Nothing"
       Just (ty, body, rest) => do
         check "decodeHandshakeMessage: type" htServerHello ty
         check "decodeHandshakeMessage: no trailing bytes" (the (List Bits8) []) rest
         check "decodeHandshakeMessage: body matches" (toHex liveServerHelloBody) (toHex body)

  -- buildClientHello: self-consistency (own decoder round-trip). The
  -- "public key" here is just arbitrary framing filler - buildClientHello
  -- doesn't validate its length, so this only exercises the surrounding
  -- message structure, not a real P-256 key_share.
  let tlsClientRandom = hexToBytes "cb34ecb1e78163ba1c38c6dacb196a6dffa21a8d9912ec18a2ef6283024dece7"
  let tlsClientPub = hexToBytes "99381de560e4bd43d23d8e435a7dbafeb3c06e51c13cae4d5413691e529aaf2c"
  case decodeHandshakeMessage (buildClientHello tlsClientRandom tlsClientPub) of
       Nothing => putStrLn "FAIL buildClientHello: not decodable as a handshake message"
       Just (ty, _, rest) => do
         check "buildClientHello: type" htClientHello ty
         check "buildClientHello: no trailing bytes" (the (List Bits8) []) rest
  where
    isLeft : Either a b -> Bool
    isLeft (Left _) = True
    isLeft (Right _) = False
