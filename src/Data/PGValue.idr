module Data.PGValue

import Data.PGTypes
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

||| One decoded result row: column name paired with its (possibly NULL)
||| text-format value, in column order.
public export
record Row where
  constructor MkRow
  columns : List (String, Maybe String)
%runElab derive "Row" [Show]

public export
toRow : RowDescription -> DataRow -> Row
toRow desc row = MkRow (zip (map name (fields desc)) (columns row))

||| Decode every row of a query result. Empty if the query had no
||| RowDescription (e.g. it was a command, not a SELECT).
public export
toRows : QueryResult -> List Row
toRows qr = case description qr of
     Nothing => []
     Just desc => map (toRow desc) (rows qr)

public export
columnByName : Row -> String -> Maybe (Maybe String)
columnByName (MkRow cols) colName = lookup colName cols

public export
getText : Row -> String -> Either String String
getText row colName =
  case columnByName row colName of
       Nothing       => Left ("No such column: " ++ colName)
       Just Nothing  => Left (colName ++ " is NULL")
       Just (Just s) => Right s

public export
getInt : Row -> String -> Either String Int
getInt row colName = do
  s <- getText row colName
  case parseInteger {a = Int} s of
       Nothing => Left ("Invalid integer in " ++ colName ++ ": " ++ s)
       Just n  => Right n

public export
getDouble : Row -> String -> Either String Double
getDouble row colName = do
  s <- getText row colName
  case parseDouble s of
       Nothing => Left ("Invalid double in " ++ colName ++ ": " ++ s)
       Just d  => Right d

public export
getBool : Row -> String -> Either String Bool
getBool row colName = do
  s <- getText row colName
  case s of
       "t"     => Right True
       "true"  => Right True
       "1"     => Right True
       "f"     => Right False
       "false" => Right False
       "0"     => Right False
       _       => Left ("Invalid boolean in " ++ colName ++ ": " ++ s)
