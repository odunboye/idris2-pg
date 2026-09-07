module UnitTests

import Data.List
import Data.PGTypes
import Helper
import Crypto.MD5
import Data.PGValue

check : Show a => Eq a => String -> a -> a -> IO ()
check label expected actual =
  if expected == actual
     then putStrLn ("OK " ++ label)
     else putStrLn ("FAIL " ++ label ++ ": expected " ++ show expected ++ ", got " ++ show actual)

strBytes : String -> List Bits8
strBytes s = map (cast . ord) (unpack s)

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
    (encode (Bind "" "" [Just (strBytes "hello"), Nothing]))

  check "Sync bytes" [0x53, 0, 0, 0, 4] (encode Sync)
  check "Terminate bytes" [0x58, 0, 0, 0, 4] (encode Terminate)
  check "CancelRequest bytes"
    ([0,0,0,16] ++ [0x04,0xd2,0x16,0x2e] ++ [0,0,0,42] ++ [0,0,0,99])
    (encode (CancelRequest 42 99))

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
    (getArray2D (MkRow [("m", Just "{{1,2},{3,4}}")]) "m")
  check "getArray2D on a 1D value reports a clear error" True
    (isLeft (getArray2D (MkRow [("m", Just "{1,2}")]) "m"))

  check "getInt ok" (Right 42) (getInt (MkRow [("n", Just "42")]) "n")
  check "getInt bad" True (isLeft (getInt (MkRow [("n", Just "abc")]) "n"))
  check "getInt null" True (isLeft (getInt (MkRow [("n", Nothing)]) "n"))
  check "getBool t" (Right True) (getBool (MkRow [("b", Just "t")]) "b")
  check "getBool f" (Right False) (getBool (MkRow [("b", Just "f")]) "b")
  check "getDouble ok" (Right 3.5) (getDouble (MkRow [("d", Just "3.5")]) "d")
  check "getInteger big" (Right 123456789012345678901234567890)
    (getInteger (MkRow [("n", Just "123456789012345678901234567890")]) "n")
  check "getDate ok" (Right (MkPGDate 2024 3 7)) (getDate (MkRow [("d", Just "2024-03-07")]) "d")
  check "getTimestamp ok" (Right (MkPGTimestamp (MkPGDate 2024 3 7) 13 45 30))
    (getTimestamp (MkRow [("ts", Just "2024-03-07 13:45:30")]) "ts")
  check "getTimestamp with fraction" (Right (MkPGTimestamp (MkPGDate 2024 3 7) 13 45 30))
    (getTimestamp (MkRow [("ts", Just "2024-03-07 13:45:30.123456")]) "ts")

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
  check "getJSON" (Right (JObject [("a", JNumber 1.0)])) (getJSON (MkRow [("j", Just "{\"a\":1}")]) "j")
  where
    isLeft : Either a b -> Bool
    isLeft (Left _) = True
    isLeft (Right _) = False
