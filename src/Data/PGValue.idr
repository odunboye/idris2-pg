module Data.PGValue

import Data.PGTypes
import public Data.PGJson
import Data.PGBinary
import Helper
import Data.List
import Data.String
import Derive.Prelude

%language ElabReflection

-- Minimal, pragmatic value decoding for basic CRUD: no pg_type round-trip
-- (unlike a full client's OID dictionary), just a hardcoded table of common
-- builtin types plus text-format parsers for the handful of Idris types a
-- typical CRUD column needs. Deliberately not a general ORM/cast machinery.

||| Common builtin Postgres type OIDs. Not exhaustive - extend as needed.
public export
data BuiltinOid
  = OidBool | OidInt2 | OidInt4 | OidInt8
  | OidText | OidVarchar
  | OidFloat4 | OidFloat8 | OidNumeric
  | OidDate | OidTimestamp | OidTimestamptz
  | OidOther Int

public export
builtinOid : Int -> BuiltinOid
builtinOid 16   = OidBool
builtinOid 20   = OidInt8
builtinOid 21   = OidInt2
builtinOid 23   = OidInt4
builtinOid 25   = OidText
builtinOid 700  = OidFloat4
builtinOid 701  = OidFloat8
builtinOid 1043 = OidVarchar
builtinOid 1082 = OidDate
builtinOid 1114 = OidTimestamp
builtinOid 1184 = OidTimestamptz
builtinOid 1700 = OidNumeric
builtinOid n    = OidOther n

public export
data ColFormat = FmtText | FmtBinary
%runElab derive "ColFormat" [Show, Eq]

toColFormat : Int -> ColFormat
toColFormat 1 = FmtBinary
toColFormat _ = FmtText

||| One decoded result row: column name, wire format, and its (possibly
||| NULL) raw value, in column order. Format is text unless the query was
||| run via queryRowsBinary.
public export
record Row where
  constructor MkRow
  columns : List (String, ColFormat, Maybe Bytes)
%runElab derive "Row" [Show]

zipCols : List FieldDescription -> List (Maybe Bytes) -> List (String, ColFormat, Maybe Bytes)
zipCols (f :: fs) (c :: cs) = (name f, toColFormat (formatCode f), c) :: zipCols fs cs
zipCols _          _        = []

public export
toRow : RowDescription -> DataRow -> Row
toRow desc row = MkRow (zipCols (fields desc) (columns row))

||| Decode every row of a query result. Empty if the query had no
||| RowDescription (e.g. it was a command, not a SELECT).
public export
toRows : QueryResult -> List Row
toRows qr = case description qr of
     Nothing => []
     Just desc => map (toRow desc) (rows qr)

getRawColumn : Row -> String -> Either String (ColFormat, Maybe Bytes)
getRawColumn (MkRow cols) colName =
  case find (\(n, _, _) => n == colName) cols of
       Nothing            => Left ("No such column: " ++ colName)
       Just (_, fmt, b)   => Right (fmt, b)

||| Text-shaped view of a column regardless of its wire format (UTF-8
||| decoding raw bytes is correct for both - Postgres's binary format for
||| text-like types is just the same UTF-8 bytes as text format). Nothing
||| if the column doesn't exist; Just Nothing if it's NULL.
public export
columnByName : Row -> String -> Maybe (Maybe String)
columnByName row colName = case getRawColumn row colName of
     Left _              => Nothing
     Right (_, Nothing)  => Just Nothing
     Right (_, Just b)   => Just (Just (bytesToString b))

public export
getText : Row -> String -> Either String String
getText row colName = do
  (_, bytes) <- getRawColumn row colName
  case bytes of
       Nothing => Left (colName ++ " is NULL")
       Just b  => Right (bytesToString b)

||| Understands both formats: text (parsed as decimal digits) and binary
||| (dispatched on byte width - 2/4/8 bytes for int2/int4/int8). See
||| queryRowsBinary's doc comment for the binary-mode type-mismatch caveat.
public export
getInt : Row -> String -> Either String Int
getInt row colName = do
  (fmt, bytes) <- getRawColumn row colName
  case bytes of
       Nothing => Left (colName ++ " is NULL")
       Just b  => case fmt of
            FmtText   => case parseInteger {a = Int} (bytesToString b) of
                 Nothing => Left ("Invalid integer in " ++ colName ++ ": " ++ bytesToString b)
                 Just n  => Right n
            FmtBinary => case decodeBinaryInt b of
                 Left err => Left ("Invalid binary integer in " ++ colName ++ ": " ++ err)
                 Right n  => Right n

||| Understands both formats: text (parsed as a decimal/exponent literal)
||| and binary (dispatched on byte width - 4 bytes for float4, 8 for
||| float8, decoded via from-scratch IEEE754 bit manipulation - see
||| Data.PGBinary). See queryRowsBinary's doc comment for the binary-mode
||| type-mismatch caveat.
public export
getDouble : Row -> String -> Either String Double
getDouble row colName = do
  (fmt, bytes) <- getRawColumn row colName
  case bytes of
       Nothing => Left (colName ++ " is NULL")
       Just b  => case fmt of
            FmtText   => case parseDouble (bytesToString b) of
                 Nothing => Left ("Invalid double in " ++ colName ++ ": " ++ bytesToString b)
                 Just d  => Right d
            FmtBinary => case decodeBinaryDouble b of
                 Left err => Left ("Invalid binary double in " ++ colName ++ ": " ++ err)
                 Right d  => Right d

||| Understands both formats: text ("t"/"true"/"1" or "f"/"false"/"0") and
||| binary (a single byte, 0 = False, nonzero = True).
public export
getBool : Row -> String -> Either String Bool
getBool row colName = do
  (fmt, bytes) <- getRawColumn row colName
  case bytes of
       Nothing => Left (colName ++ " is NULL")
       Just b  => case fmt of
            FmtText   => case bytesToString b of
                 "t"     => Right True
                 "true"  => Right True
                 "1"     => Right True
                 "f"     => Right False
                 "false" => Right False
                 "0"     => Right False
                 s       => Left ("Invalid boolean in " ++ colName ++ ": " ++ s)
            FmtBinary => case decodeBinaryBool b of
                 Left err => Left ("Invalid binary boolean in " ++ colName ++ ": " ++ err)
                 Right v  => Right v

||| Arbitrary-precision, for `numeric`/`bigint` values that don't fit `Int`.
||| In binary mode this only understands int2/int4/int8 (dispatched by
||| byte width, then widened) - binary `numeric`'s own wire format is a
||| distinct, more involved encoding that isn't supported here.
public export
getInteger : Row -> String -> Either String Integer
getInteger row colName = do
  (fmt, bytes) <- getRawColumn row colName
  case bytes of
       Nothing => Left (colName ++ " is NULL")
       Just b  => case fmt of
            FmtText   => case parseInteger {a = Integer} (bytesToString b) of
                 Nothing => Left ("Invalid integer in " ++ colName ++ ": " ++ bytesToString b)
                 Just n  => Right n
            FmtBinary => case decodeBinaryInt b of
                 Left err => Left ("Invalid binary integer in " ++ colName ++ ": " ++ err)
                 Right n  => Right (cast n)

public export
record PGDate where
  constructor MkPGDate
  year, month, day : Int
%runElab derive "PGDate" [Show, Eq]

public export
record PGTimestamp where
  constructor MkPGTimestamp
  date : PGDate
  hour, minute, second : Int
%runElab derive "PGTimestamp" [Show, Eq]

-- Parses Postgres's default "YYYY-MM-DD" date output. Returns whatever
-- follows it too, so getTimestamp can reuse this for the date portion.
parsePGDate : String -> Maybe (PGDate, String)
parsePGDate s = case unpack s of
     (y1::y2::y3::y4::'-'::mo1::mo2::'-'::d1::d2::rest) => do
       y  <- parsePositive {a = Int} (pack [y1, y2, y3, y4])
       mo <- parsePositive {a = Int} (pack [mo1, mo2])
       d  <- parsePositive {a = Int} (pack [d1, d2])
       Just (MkPGDate y mo d, pack rest)
     _ => Nothing

parsePGTime : String -> Maybe (Int, Int, Int)
parsePGTime s = case unpack s of
     (h1::h2::':'::mi1::mi2::':'::s1::s2::_) => do
       h  <- parsePositive {a = Int} (pack [h1, h2])
       mi <- parsePositive {a = Int} (pack [mi1, mi2])
       se <- parsePositive {a = Int} (pack [s1, s2])
       Just (h, mi, se)
     _ => Nothing

public export
getDate : Row -> String -> Either String PGDate
getDate row colName = do
  s <- getText row colName
  case parsePGDate s of
       Just (d, _) => Right d
       Nothing     => Left ("Invalid date in " ++ colName ++ ": " ++ s)

||| Parses "YYYY-MM-DD HH:MI:SS[.ffffff][+TZ]" (Postgres's default text
||| output for `timestamp`/`timestamptz`). Fractional seconds and any
||| timezone offset suffix are parsed past but not retained - there's no
||| timezone-aware type here.
public export
getTimestamp : Row -> String -> Either String PGTimestamp
getTimestamp row colName = do
  s <- getText row colName
  case parsePGDate s of
       Nothing => Left ("Invalid timestamp in " ++ colName ++ ": " ++ s)
       Just (d, rest) => case parsePGTime (trim rest) of
            Nothing            => Left ("Invalid timestamp in " ++ colName ++ ": " ++ s)
            Just (h, mi, se) => Right (MkPGTimestamp d h mi se)

||| Postgres's canonical array text output ("{a,b,"c,d",NULL}") parses into
||| this tree: a leaf is a scalar element (Nothing for an unquoted NULL
||| marker), a group is one level of "{...}" nesting - so an N-dimensional
||| array is N groups deep, each holding the next level's groups/leaves.
public export
data PGArrayValue = PGLeaf (Maybe String) | PGGroup (List PGArrayValue)
%runElab derive "PGArrayValue" [Show, Eq]

-- A recursive-descent parser (rather than the flat single-pass scan a
-- one-dimensional-only version could use), since correctly matching nested
-- "{...}" groups needs real recursion, not just quote-tracking.
--
-- Postgres always quotes an element that would otherwise be ambiguous with
-- the NULL marker (or contain a comma/brace/backslash/quote/whitespace), so
-- an *unquoted* NULL token unambiguously means a null element, never the
-- literal text "NULL".
toElement : Bool -> List Char -> Maybe String
toElement wasQuoted cs =
  let str = pack cs
  in if not wasQuoted && str == "NULL" then Nothing else Just str

-- A budget on remaining "{...}" nesting, decremented only when a new group
-- opens - without it, a deeply nested server-supplied array text could
-- exhaust the call stack (parseValue/parseGroup recurse into each other
-- once per nesting level). Exported so tests can check the exact boundary
-- rather than duplicating the number.
public export
maxArrayDepth : Nat
maxArrayDepth = 100

parseValue : (depth : Nat) -> List Char -> Either String (PGArrayValue, List Char)
parseGroup : (depth : Nat) -> List Char -> List PGArrayValue -> Either String (PGArrayValue, List Char)
parseScalar : List Char -> Either String (PGArrayValue, List Char)
parseQuoted : List Char -> List Char -> Either String (PGArrayValue, List Char)
spanScalar : List Char -> (List Char, List Char)

parseValue depth ('{' :: rest) = case depth of
     Z        => Left "array nesting too deep"
     S depth' => parseGroup depth' rest []
parseValue depth cs            = parseScalar cs

parseGroup depth ('}' :: rest) acc = Right (PGGroup (reverse acc), rest)
parseGroup depth cs            acc = do
  (v, rest) <- parseValue depth cs
  case rest of
       (',' :: rest') => parseGroup depth rest' (v :: acc)
       ('}' :: rest') => Right (PGGroup (reverse (v :: acc)), rest')
       _              => Left "expected ',' or '}' in array"

parseScalar ('"' :: rest) = parseQuoted rest []
parseScalar cs            = let (chars, rest) = spanScalar cs
                             in Right (PGLeaf (toElement False chars), rest)

parseQuoted []                  acc = Left "unterminated quoted array element"
parseQuoted ('\\' :: c :: rest) acc = parseQuoted rest (acc ++ [c])
parseQuoted ('"' :: rest)       acc = Right (PGLeaf (toElement True acc), rest)
parseQuoted (c :: rest)         acc = parseQuoted rest (acc ++ [c])

spanScalar []                       = ([], [])
spanScalar (c :: cs) =
  if c == ',' || c == '}'
     then ([], c :: cs)
     else let (more, rest) = spanScalar cs in (c :: more, rest)

||| Parses any Postgres array text output, of any dimensionality.
public export
parsePGArrayValue : String -> Either String PGArrayValue
parsePGArrayValue s = case unpack s of
     ('{' :: rest) => case parseGroup maxArrayDepth rest [] of
          Right (v, []) => Right v
          Right (_, _)  => Left "trailing content after array value"
          Left err      => Left err
     _ => Left "array value must start with '{'"

public export
getNestedArray : Row -> String -> Either String PGArrayValue
getNestedArray row colName = getText row colName >>= parsePGArrayValue

toLeaf : PGArrayValue -> Either String (Maybe String)
toLeaf (PGLeaf x)   = Right x
toLeaf (PGGroup _)  = Left "expected a scalar, found a nested array"

toLeafRow : PGArrayValue -> Either String (List (Maybe String))
toLeafRow (PGGroup xs) = traverse toLeaf xs
toLeafRow (PGLeaf _)   = Left "expected a nested array, found a scalar"

||| One-dimensional array, e.g. `int[]`/`text[]`. Errors clearly if the
||| value actually has more than one dimension, rather than misparsing it.
public export
parsePGArray : String -> Either String (List (Maybe String))
parsePGArray s = do
  v <- parsePGArrayValue s
  case v of
       PGGroup xs => traverse toLeaf xs
       PGLeaf _   => Left "expected an array, found a scalar"

public export
getArray : Row -> String -> Either String (List (Maybe String))
getArray row colName = getText row colName >>= parsePGArray

||| Two-dimensional array, e.g. `int[][]`: a list of rows of scalars.
public export
getArray2D : Row -> String -> Either String (List (List (Maybe String)))
getArray2D row colName = do
  v <- getNestedArray row colName
  case v of
       PGGroup rows => traverse toLeafRow rows
       PGLeaf _     => Left "expected a 2D array, found a scalar"

||| Decodes a `json`/`jsonb` column via the minimal parser in Data.PGJson
||| (JSONValue is re-exported from this module, so callers only need to
||| import Data.PGValue).
public export
getJSON : Row -> String -> Either String JSONValue
getJSON row colName = getText row colName >>= parseJSON
