module Helper

import Network.Socket
import Data.Bits
import Data.List
import Data.Maybe
import Data.PGTypes
import Network.Core
import Network.RawSocket
import Crypto.MD5
import Derive.Prelude


data SocketState = Connected | UnKnown

getSock : IO (Either SocketError Socket)
getSock = socket AF_INET Stream 0 

export
getConnection :  Socket -> SocketAddress -> Port ->  IO (Maybe Socket)
getConnection s addr p= do
         res <- connect s addr p
         case res of 
              0 => do 
                pure (Just (s))
              _ => do
                pure Nothing

public export
bytesToString : List Bits8 -> String
bytesToString bs = pack (map (chr . cast) bs)

public export
toInt : Vect 4 Bits8 ->  Int
toInt [x, y, z, w] = ((cast x) `shiftL` 24)  
  .|. ((cast y) `shiftL` 16)
  .|. ((cast z) `shiftL` 8)
  .|. cast w

-- Encode/decode 16-bit and 32-bit integers (big endian)
public export
encodeInt16 : Int -> List Bits8
encodeInt16 n =
  [ fromInteger (cast((shiftR n 8) .&. 0xFF))
  , fromInteger (cast(n .&. 0xFF))
  ]

public export
encodeInt32 : Int -> List Bits8
encodeInt32 n =
  [ fromInteger (cast((shiftR n 24) .&. 0xFF))
  , fromInteger (cast((shiftR n 16) .&. 0xFF))
  , fromInteger (cast((shiftR n 8) .&. 0xFF))
  , fromInteger (cast(n .&. 0xFF))
  ]

public export
decodeInt16 : List Bits8 -> Either String (Int, List Bits8)
decodeInt16 (b1 :: b2 :: rest) =
  Right (shiftL (cast b1) 8 + cast b2, rest)
decodeInt16 _ = Left "decodeInt16: insufficient bytes"

public export
decodeInt32 : List Bits8 -> Either String (Int, List Bits8)
decodeInt32 (b1 :: b2 :: b3 :: b4 :: rest) =
  Right ( shiftL (cast b1) 24
        + shiftL (cast b2) 16
        + shiftL (cast b3) 8
        + cast b4
        , rest)
decodeInt32 _ = Left "decodeInt32: insufficient bytes"

-- Encode/decode null-terminated UTF8 string
public export
encodeCString : String -> List Bits8
encodeCString s = map cast (unpack s) ++ [0]

public export
decodeCString : List Bits8 -> Either String (String, List Bits8)
decodeCString bs =
  case span (/= 0) bs of
    (chars, 0 :: rest) => Right (pack (map cast chars), rest)
    _ => Left "decodeCString: unterminated string"

eitherToMaybe : Either e a -> Maybe a
eitherToMaybe (Left _) = Nothing
eitherToMaybe (Right v) = Just v

public export
decodeFieldDesc : List Bits8 -> Maybe (FieldDescription, List Bits8)
decodeFieldDesc bs = do
  (name, afterName) <- eitherToMaybe (decodeCString bs)
  (tableOID, a1) <- eitherToMaybe (decodeInt32 afterName)
  (colAttr, a2) <- eitherToMaybe (decodeInt16 a1)
  (typeOID, a3) <- eitherToMaybe (decodeInt32 a2)
  (typeSize, a4) <- eitherToMaybe (decodeInt16 a3)
  (typeMod, a5) <- eitherToMaybe (decodeInt32 a4)
  (formatCode, rest) <- eitherToMaybe (decodeInt16 a5)
  pure (MkFieldDescription name tableOID colAttr typeOID typeSize typeMod formatCode, rest)

public export
decodeRowDescFields : Int -> List Bits8 -> Maybe (List FieldDescription)
decodeRowDescFields 0 bs = Just []
decodeRowDescFields n bs = do
  (field, rest) <- decodeFieldDesc bs
  more <- decodeRowDescFields (n - 1) rest
  pure (field :: more)

-- ErrorResponse/NoticeResponse payload: a sequence of (1-byte field code,
-- null-terminated string) pairs, terminated by a final 0x00 byte.
public export
decodeNoticeFields : Bytes -> Either String (List NoticeField)
decodeNoticeFields [] = Right []
decodeNoticeFields (0 :: _) = Right []
decodeNoticeFields (tagByte :: rest) = do
  (val, afterVal) <- decodeCString rest
  more <- decodeNoticeFields afterVal
  Right (MkField (chr (cast tagByte)) val :: more)

fieldValue : Char -> List NoticeField -> Maybe String
fieldValue c [] = Nothing
fieldValue c (f :: fs) = if tag f == c then Just (value f) else fieldValue c fs

public export
mkError : List NoticeField -> Error
mkError fields = MkError (fieldValue 'S' fields) (fieldValue 'C' fields)
                          (fromMaybe "" (fieldValue 'M' fields))

public export
decodeInt32List : Nat -> Bytes -> Either String (List Int)
decodeInt32List Z bs = Right []
decodeInt32List (S k) bs = do
  (oid, rest) <- decodeInt32 bs
  more <- decodeInt32List k rest
  Right (oid :: more)


public export
readFrameBit : (PGConnection Connected) -> IO (Either String FrameBytes)
readFrameBit conn = do
  let connx = (MkConnected (socket conn))
  msgTypeResp <- receiveExact connx 1
  case msgTypeResp of
       (Left x) => pure (Left x)
       (Right tagByte) => do
          lenRes <- receiveExact connx 4
          case lenRes of
              (Left x) => pure (Left x)
              (Right lenList) => do
                    let vect = toVect 4 lenList
                    case vect of
                         Nothing => pure (Left "Error parsing length")
                         (Just lenVect) => do
                           payloadRes <- receiveExact connx ((toInt lenVect) - 4)
                           case payloadRes of
                                (Left y) => pure (Left y)
                                (Right y) => pure (Right(MkFrameBytes tagByte lenList y))


public export
connectPG : String -> Int -> IO (Maybe (PGConnection Connected))
connectPG host port = do
  sockRes <- getSock
  case sockRes of
    Left _ => pure Nothing
    Right socket => do
      connRes <- getConnection socket (IPv4Addr 127 0 0 1) port
      case connRes of
        Nothing => pure Nothing
        Just _  => pure (Just (MkPGConnection socket []))


public export
sendStartup : PGConnection Connected -> List Bits8 -> IO (Maybe (PGConnection StartupSent))
sendStartup conn msg = do
  let conx = MkConnected (socket conn)
  res <- send conx msg
  case res of
       (Left x) => pure Nothing
       (Right x) => pure (Just(MkPGConnection (socket conn) []))

parseColumns : Nat -> Bytes -> Either String (List (Maybe String))
parseColumns Z rest = Right []
parseColumns (S k) bs = do
  (len, afterLen) <- decodeInt32 bs
  case len == -1 of
      True => do
        rest <- parseColumns k afterLen
        Right (Nothing :: rest)
      False => do
        let val = bytesToString (take (cast len) afterLen)
        rest <- parseColumns k (drop (cast len) afterLen)
        Right (Just val :: rest)


public export
encode : PGMsg -> Bytes
encode (StartupMsg proto params) =
  let keyvals = concatMap (\(k, v) => encodeCString k ++ encodeCString v) params
      proto  = [0x00, 0x03, 0x00, 0x00]  -- protocol 3.0
      payload = proto ++ keyvals ++[0] --encodeInt32 proto ++ keyvals ++ [0]  -- terminator
      len = 4 + length payload
  in  encodeInt32 (cast len) ++ payload

encode (QueryMsg query) =
  let payload = encodeCString (body query)
      len = 4 + length payload
      in [toByte QueryTag] ++ encodeInt32 (cast len) ++ payload

encode (PasswordMessage pw) =
  let payload = encodeCString pw
      len = 4 + length payload
  in [0x70] ++ encodeInt32 (cast len) ++ payload  -- 'p'

encode Terminate = [0x58] ++ encodeInt32 4  -- 'X', no payload

encode _ =  ?unimplementedEncode

public export
decode : FrameBytes -> Either String PGMsg
decode (MkFrameBytes [] len payload) = Left "Tag is Empty"
decode (MkFrameBytes (x :: xs) [] payload) = Left "Length is Empty"
decode (MkFrameBytes (tag :: xs) (y :: ys) payload) = do
  case tagFromString (bytesToString [tag]) of
       AuthenticationTag => case decodeInt32 payload of
            Right (authCode, salt) => Right (AuthenticationMsg (parseAuthResponse authCode salt))
            Left e => Left e

       BackendKeyDataTag => case decodeInt32 payload of
            Right (pid, afterPid) =>
              case decodeInt32 afterPid of
                Right (secret, _) => Right (BackendKeyDataMsg (MkBackendKeyData pid secret))
                Left e => Left e
            Left e => Left e

       BindCompleteTag => Right BindCompleteMsg
       CloseCompleteTag => Right CloseCompleteMsg

       CommandCompleteTag => case decodeCString payload of
            Right (s, _) => Right (CommandCompleteMsg s)
            Left e => Left e

       DataRowTag => do
         (nCols, rest) <- decodeInt16 payload
         let datarows = parseColumns (cast nCols) rest
         case datarows of
              (Left err) => Left err
              (Right x) => Right (DataRowMsg (MkDataRow nCols x))


       EmptyQueryResponseTag => Right EmptyQueryResponseMsg

       ErrorResponseTag => case decodeNoticeFields payload of
            Right fields => Right (ErrorMsg (mkError fields))
            Left e => Left e

       NoticeResponseTag => case decodeNoticeFields payload of
            Right fields => Right (NoticeMsg (MkNotice fields))
            Left e => Left e

       NotificationResponseTag => Right (UnknownMsg NotificationResponseTag payload)

       ParameterDescriptionTag => case decodeInt16 payload of
            Right (n, rest) => case decodeInt32List (cast n) rest of
                 Right oids => Right (ParameterDescriptionMsg oids)
                 Left e => Left e
            Left e => Left e

       ParameterStatusTag => case decodeCString payload of
            Right (key, afterKey) =>
              case decodeCString afterKey of
                Right (val, _) => Right (ParameterStatusMsg (MkParameterStatus key val))
                Left e => Left e
            Left e => Left e

       ParseCompleteTag => Right ParseCompleteMsg
       PortalSuspendedTag => Right PortalSuspendedMsg
       ReadyForQueryTag => do
          case payload of
            [b] => Right (ReadyForQueryMsg (fromByte b))
            _   => Left "Invalid ReadyForQuery payload"

       RowDescriptionTag => case decodeInt16 payload of
            Right (nfields, rest) =>
              case decodeRowDescFields nfields rest of
                Just fields => Right (RowDescriptionMsg (MkRowDescription fields))
                Nothing => Left "Failed to parse RowDescription fields"
            Left e => Left e

       QueryTag => Right (UnknownMsg QueryTag payload)
       (UnknownTag str) => Right (UnknownMsg (UnknownTag str) payload)

public export
readFrame : PGConnection Connected -> IO (Either String PGMsg)
readFrame conn = do
  frameRes <- readFrameBit conn
  case frameRes of
       (Left err) => pure (Left err)
       (Right frameBytes) => do
         --let bytes = frameBytesToList frameBytes
         case (decode frameBytes) of
             (Left err) => pure (Left err)
             (Right msg) => pure (Right msg)


public export
waitForReady : Nat -> PGConnection Connected -> IO (Either String  (PGConnection Ready))
waitForReady Z conn = pure (Left "Error: exceeded maximum message depth before ReadyForQuery")
waitForReady(S k) conn = do
  frameRes <- readFrame conn
  case frameRes of
       (Left err) => pure (Left err)
       (Right (ReadyForQueryMsg c)) => pure (Right (MkPGConnection (socket conn) []))
       (Right _) => waitForReady k conn


startupstep : StartupResult -> PGMsg -> StartupResult
startupstep acc (AuthenticationMsg a) = { authState := Just a } acc 
startupstep acc (ParameterStatusMsg p)= { params := acc.params ++ [p] } acc
startupstep acc (BackendKeyDataMsg b) = { backendKey := Just b } acc
startupstep acc (ReadyForQueryMsg r)  = { ready := Just (MkReadyForQuery r) } acc
startupstep acc (ErrorMsg e)          = { errors := acc.errors ++ [e] } acc
startupstep acc (NoticeMsg n)         = { notices := acc.notices ++ [n] } acc
startupstep acc _                     = acc


public export
handleStartupResponse : (user : String) -> (password : String) -> PGConnection Connected -> IO StartupResult
handleStartupResponse user password conn = go init
  where
    init : StartupResult
    init = MkStartupResult Nothing [] Nothing Nothing [] []

    fail : StartupResult -> String -> StartupResult
    fail acc msg = { errors := acc.errors ++ [MkError Nothing Nothing msg] } acc

    sendPassword : StartupResult -> String -> IO StartupResult
    sendPassword acc pw = do
      res <- send (MkConnected (socket conn)) (encode (PasswordMessage pw))
      case res of
           Left err => pure (fail acc err)
           Right () => pure acc

    go : StartupResult -> IO StartupResult
    go acc = do
      bs <- readFrame conn
      case bs of
        Left err => pure (fail acc err)
        Right msg =>
              case msg of
                ReadyForQueryMsg r => pure ({ ready := Just (MkReadyForQuery r) } acc)
                AuthenticationMsg AuthOk => go ({ authState := Just AuthOk } acc)
                AuthenticationMsg AuthCleartext => do
                  acc' <- sendPassword acc password
                  go ({ authState := Just AuthCleartext } acc')
                AuthenticationMsg (AuthMD5 salt) => do
                  let hashed = pgMD5Password password user salt
                  acc' <- sendPassword acc hashed
                  go ({ authState := Just (AuthMD5 salt) } acc')
                AuthenticationMsg AuthSASL =>
                  pure (fail acc "SCRAM-SHA-256 (SASL) authentication is not supported")
                AuthenticationMsg (AuthUnknown n) =>
                  pure (fail acc ("Unsupported authentication method: " ++ show n))
                _                  => go (startupstep acc msg)


querystep : QueryResult -> PGMsg -> QueryResult
querystep acc (RowDescriptionMsg rd) = { description := Just rd } acc
querystep acc (DataRowMsg row)       = { rows := acc.rows ++ [row] } acc 
querystep acc (CommandCompleteMsg c) = { commandTag := Just c } acc 
querystep acc (ReadyForQueryMsg r)   = { status := Just (MkReadyForQuery r) } acc 
querystep acc (ErrorMsg e)           = { errors := acc.errors ++ [e] } acc 
querystep acc (NoticeMsg n)          = { notices := acc.notices ++ [n] } acc 
querystep acc _                      = acc


public export
handleQueryResponse : DB -> IO QueryResult
handleQueryResponse db = go (MkQueryResult Nothing [] Nothing Nothing [] [])
  where
    go : QueryResult -> IO QueryResult
    go acc = do
      bs <- readFrame (conn db)
      case bs of
        Left err => pure ({ errors := acc.errors ++ [MkError Nothing Nothing err] } acc)
        Right msg =>
              case msg of
                ReadyForQueryMsg r => pure ({ status := Just (MkReadyForQuery r) } acc)
                _                  => go (querystep acc msg)
