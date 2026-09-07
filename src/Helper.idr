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

-- Raw (non-null-terminated) UTF8 bytes, for extended-protocol parameter values.
public export
stringToBytes : String -> Bytes
stringToBytes s = map cast (unpack s)

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
                          (fromMaybe "" (fieldValue 'M' fields)) fields

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
      -- Hostname is resolved via getaddrinfo at the C layer, which handles
      -- both real hostnames and dotted-quad/numeric addresses.
      connRes <- getConnection socket (Hostname host) port
      case connRes of
        Nothing => do
          Network.Socket.close socket
          pure Nothing
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

encode (Parse stmtName query paramTypes) =
  let payload = encodeCString stmtName ++ encodeCString query
                  ++ encodeInt16 (cast (length paramTypes))
                  ++ concatMap encodeInt32 paramTypes
      len = 4 + length payload
  in [0x50] ++ encodeInt32 (cast len) ++ payload  -- 'P'

encode (Bind portal stmtName params) =
  let encodeParam : Maybe Bytes -> Bytes
      encodeParam Nothing = encodeInt32 (-1)
      encodeParam (Just bytes) = encodeInt32 (cast (length bytes)) ++ bytes
      payload = encodeCString portal ++ encodeCString stmtName
                  ++ encodeInt16 0  -- all parameters are text format
                  ++ encodeInt16 (cast (length params))
                  ++ concatMap encodeParam params
                  ++ encodeInt16 0  -- all results in text format
      len = 4 + length payload
  in [0x42] ++ encodeInt32 (cast len) ++ payload  -- 'B'

encode (Describe kind name) =
  let payload = [cast (ord kind)] ++ encodeCString name
      len = 4 + length payload
  in [0x44] ++ encodeInt32 (cast len) ++ payload  -- 'D'

encode (Execute portal maxRows) =
  let payload = encodeCString portal ++ encodeInt32 maxRows
      len = 4 + length payload
  in [0x45] ++ encodeInt32 (cast len) ++ payload  -- 'E'

encode Sync = [0x53] ++ encodeInt32 4  -- 'S', no payload

-- No tag byte: just length(=16), the fixed cancel-request magic code, pid, secret.
encode (CancelRequest pgPid pgSecret) =
  encodeInt32 16 ++ encodeInt32 80877102 ++ encodeInt32 pgPid ++ encodeInt32 pgSecret

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

       NotificationResponseTag => case decodeInt32 payload of
            Right (pgPid, afterPid) => case decodeCString afterPid of
                 Right (channel, afterChannel) => case decodeCString afterChannel of
                      Right (msg, _) => Right (NotificationMsg (MkNotification pgPid channel msg))
                      Left e => Left e
                 Left e => Left e
            Left e => Left e

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
       (Right frameBytes) => case (decode frameBytes) of
             (Left err) => pure (Left err)
             (Right msg) => pure (Right msg)


startupstep : StartupResult -> PGMsg -> StartupResult
startupstep acc (AuthenticationMsg a) = { authState := Just a } acc 
startupstep acc (ParameterStatusMsg p)= { params := acc.params ++ [p] } acc
startupstep acc (BackendKeyDataMsg b) = { backendKey := Just b } acc
startupstep acc (ReadyForQueryMsg r)  = { ready := Just (MkReadyForQuery r) } acc
startupstep acc (ErrorMsg e)          = { errors := acc.errors ++ [e] } acc
startupstep acc (NoticeMsg n)         = { notices := acc.notices ++ [n] } acc
startupstep acc _                     = acc


public export
handleStartupResponse : (user : String) -> (password : String) -> PGConnection Connected -> IO (Either PGError StartupResult)
handleStartupResponse user password conn = go init
  where
    init : StartupResult
    init = MkStartupResult Nothing [] Nothing Nothing [] []

    -- Nothing on the wire went wrong, but this session can't proceed
    -- (unsupported auth method) - a protocol-level failure, not a query error.
    unsupported : String -> IO (Either PGError StartupResult)
    unsupported msg = pure (Left (ProtocolError msg))

    sendPassword : String -> IO (Either PGError ())
    sendPassword pw = do
      res <- send (MkConnected (socket conn)) (encode (PasswordMessage pw))
      case res of
           Left err => pure (Left (ConnectionError err))
           Right () => pure (Right ())

    go : StartupResult -> IO (Either PGError StartupResult)
    go acc = do
      bs <- readFrame conn
      case bs of
        Left err => pure (Left (ConnectionError err))
        Right msg =>
              case msg of
                ReadyForQueryMsg r => pure (Right ({ ready := Just (MkReadyForQuery r) } acc))
                AuthenticationMsg AuthOk => go ({ authState := Just AuthOk } acc)
                AuthenticationMsg AuthCleartext => do
                  sent <- sendPassword password
                  case sent of
                       Left err => pure (Left err)
                       Right () => go ({ authState := Just AuthCleartext } acc)
                AuthenticationMsg (AuthMD5 salt) => do
                  let hashed = pgMD5Password password user salt
                  sent <- sendPassword hashed
                  case sent of
                       Left err => pure (Left err)
                       Right () => go ({ authState := Just (AuthMD5 salt) } acc)
                AuthenticationMsg AuthSASL =>
                  unsupported "SCRAM-SHA-256 (SASL) authentication is not supported"
                AuthenticationMsg (AuthUnknown n) =>
                  unsupported ("Unsupported authentication method: " ++ show n)
                _                  => go (startupstep acc msg)


querystep : QueryResult -> PGMsg -> QueryResult
querystep acc (RowDescriptionMsg rd) = { description := Just rd } acc
querystep acc (DataRowMsg row)       = { rows := acc.rows ++ [row] } acc
querystep acc (ErrorMsg e)           = { errors := acc.errors ++ [e] } acc
querystep acc (NoticeMsg n)          = { notices := acc.notices ++ [n] } acc
querystep acc _                      = acc

emptyQueryResult : QueryResult
emptyQueryResult = MkQueryResult Nothing [] Nothing Nothing [] []

setStatusOnLast : ReadyForQuery -> List QueryResult -> List QueryResult
setStatusOnLast r []        = [{ status := Just r } emptyQueryResult]
setStatusOnLast r [x]       = [{ status := Just r } x]
setStatusOnLast r (x :: xs) = x :: setStatusOnLast r xs

-- Postgres's simple query protocol allows multiple ';'-separated statements
-- in one Query message, each yielding its own RowDescription/DataRow*/
-- CommandComplete (or EmptyQueryResponse for a blank statement) before a
-- single final ReadyForQuery. `pending` accumulates the statement currently
-- in progress; it flushes into `completed` at each CommandComplete/
-- EmptyQueryResponse boundary, so each statement gets its own QueryResult
-- instead of one merged/corrupted result.
public export
handleQueryResponses : DB -> IO (Either PGError (List QueryResult))
handleQueryResponses db = go Nothing []
  where
    go : Maybe QueryResult -> List QueryResult -> IO (Either PGError (List QueryResult))
    go pending completed = do
      bs <- readFrame (conn db)
      case bs of
        Left err => pure (Left (ConnectionError err))
        Right msg =>
          let acc = fromMaybe emptyQueryResult pending in
          case msg of
               ReadyForQueryMsg r =>
                 case pending of
                      Nothing => pure (Right (setStatusOnLast (MkReadyForQuery r) completed))
                      Just _  => pure (Right (completed ++ [{ status := Just (MkReadyForQuery r) } acc]))
               CommandCompleteMsg c => go Nothing (completed ++ [{ commandTag := Just c } acc])
               EmptyQueryResponseMsg => go Nothing (completed ++ [acc])
               _ => go (Just (querystep acc msg)) completed
