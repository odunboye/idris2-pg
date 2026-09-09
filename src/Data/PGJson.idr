module Data.PGJson

import Data.String
import Derive.Prelude

%language ElabReflection

-- A minimal JSON parser, for decoding Postgres json/jsonb columns without
-- pulling in an external JSON/parser-combinator library dependency -
-- consistent with this project's from-scratch approach elsewhere (see
-- Crypto.MD5). JSON's grammar is simple enough that this is a much smaller
-- undertaking than that was.

public export
data JSONValue
  = JNull
  | JBool Bool
  | JNumber Double
  | JString String
  | JArray (List JSONValue)
  | JObject (List (String, JSONValue))
%runElab derive "JSONValue" [Show, Eq]

isWs : Char -> Bool
isWs c = c == ' ' || c == '\t' || c == '\n' || c == '\r'

skipWs : List Char -> List Char
skipWs (c :: cs) = if isWs c then skipWs cs else (c :: cs)
skipWs [] = []

stripLit : String -> List Char -> Maybe (List Char)
stripLit lit cs =
  let litChars = unpack lit
      (pre, rest) = splitAt (length litChars) cs
  in if pre == litChars then Just rest else Nothing

isDigit' : Char -> Bool
isDigit' c = c >= '0' && c <= '9'

hexDigitVal : Char -> Maybe Int
hexDigitVal c =
  if isDigit' c then Just (cast (ord c) - cast (ord '0'))
  else if c >= 'a' && c <= 'f' then Just (cast (ord c) - cast (ord 'a') + 10)
  else if c >= 'A' && c <= 'F' then Just (cast (ord c) - cast (ord 'A') + 10)
  else Nothing

-- Combines exactly 4 hex digits into one code point. Doesn't merge UTF-16
-- surrogate pairs (a \uD800-\uDFFF escape decodes to that raw code point
-- rather than the intended character) - a known limitation, same spirit as
-- getTimestamp not retaining a timezone offset.
hex4 : List Char -> Maybe Int
hex4 [a, b, c, d] = do
  va <- hexDigitVal a; vb <- hexDigitVal b; vc <- hexDigitVal c; vd <- hexDigitVal d
  Just (va * 4096 + vb * 256 + vc * 16 + vd)
hex4 _ = Nothing

parseString : List Char -> Either String (String, List Char)
parseString cs = go cs []
  where
    go : List Char -> List Char -> Either String (String, List Char)
    go [] acc = Left "unterminated JSON string"
    go ('"' :: rest) acc = Right (pack (reverse acc), rest)
    go ('\\' :: 'u' :: h1 :: h2 :: h3 :: h4 :: rest) acc =
      case hex4 [h1, h2, h3, h4] of
           Just code => go rest (chr code :: acc)
           Nothing   => Left "invalid \\u escape in JSON string"
    go ('\\' :: c :: rest) acc =
      case c of
           '"'  => go rest ('"' :: acc)
           '\\' => go rest ('\\' :: acc)
           '/'  => go rest ('/' :: acc)
           'b'  => go rest (chr 8 :: acc)
           'f'  => go rest (chr 12 :: acc)
           'n'  => go rest ('\n' :: acc)
           'r'  => go rest ('\r' :: acc)
           't'  => go rest ('\t' :: acc)
           _    => Left ("invalid escape \\" ++ singleton c ++ " in JSON string")
    go (c :: rest) acc = go rest (c :: acc)

isNumChar : Char -> Bool
isNumChar c = isDigit' c || c == '-' || c == '+' || c == '.' || c == 'e' || c == 'E'

parseNumber : List Char -> Either String (JSONValue, List Char)
parseNumber cs = case span isNumChar cs of
     ([], _)          => Left "expected a JSON value"
     (numChars, rest) => case parseDouble (pack numChars) of
          Just d  => Right (JNumber d, rest)
          Nothing => Left ("invalid JSON number: " ++ pack numChars)

-- A budget on remaining container nesting, decremented only at points that
-- open a new '{'/'[' - without it, deeply nested server-supplied JSON text
-- could exhaust the call stack (these three functions recurse into each
-- other once per nesting level).
maxJSONDepth : Nat
maxJSONDepth = 100

parseVal : (depth : Nat) -> List Char -> Either String (JSONValue, List Char)
parseArrayBody : (depth : Nat) -> List Char -> List JSONValue -> Either String (JSONValue, List Char)
parseObjectBody : (depth : Nat) -> List Char -> List (String, JSONValue) -> Either String (JSONValue, List Char)

parseVal depth cs = case skipWs cs of
     ('"' :: rest) => do
       (s, rest') <- parseString rest
       Right (JString s, rest')
     ('{' :: rest) => case depth of
          Z      => Left "JSON nesting too deep"
          S depth' => parseObjectBody depth' (skipWs rest) []
     ('[' :: rest) => case depth of
          Z      => Left "JSON nesting too deep"
          S depth' => parseArrayBody depth' (skipWs rest) []
     cs' => case stripLit "true" cs' of
          Just rest => Right (JBool True, rest)
          Nothing   => case stripLit "false" cs' of
               Just rest => Right (JBool False, rest)
               Nothing   => case stripLit "null" cs' of
                    Just rest => Right (JNull, rest)
                    Nothing   => parseNumber cs'

parseArrayBody depth cs acc = case skipWs cs of
     (']' :: rest) => Right (JArray (reverse acc), rest)
     cs' => do
       (v, rest) <- parseVal depth cs'
       case skipWs rest of
            (',' :: rest') => parseArrayBody depth (skipWs rest') (v :: acc)
            (']' :: rest') => Right (JArray (reverse (v :: acc)), rest')
            _              => Left "expected ',' or ']' in JSON array"

parseObjectBody depth cs acc = case skipWs cs of
     ('}' :: rest) => Right (JObject (reverse acc), rest)
     ('"' :: rest) => do
       (key, afterKey) <- parseString rest
       case skipWs afterKey of
            (':' :: afterColon) => do
              (v, afterVal) <- parseVal depth (skipWs afterColon)
              case skipWs afterVal of
                   (',' :: rest') => parseObjectBody depth (skipWs rest') ((key, v) :: acc)
                   ('}' :: rest') => Right (JObject (reverse ((key, v) :: acc)), rest')
                   _              => Left "expected ',' or '}' in JSON object"
            _ => Left "expected ':' after JSON object key"
     _ => Left "expected '\"' to start a JSON object key"

public export
parseJSON : String -> Either String JSONValue
parseJSON s = do
  (v, rest) <- parseVal maxJSONDepth (unpack s)
  case skipWs rest of
       [] => Right v
       _  => Left "trailing content after JSON value"
