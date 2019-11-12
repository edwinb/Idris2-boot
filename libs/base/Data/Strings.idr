module Data.Strings

import Data.List

export
singleton : Char -> String
singleton c = strCons c ""

-- This works quickly because when string-append builds the result, it allocates
-- enough room in advance so there's only one allocation, rather than lots!
export
fastAppend : List String -> String
fastAppend xs = unsafePerformIO (schemeCall String "string-append" (toFArgs xs))
  where
    toFArgs : List String -> FArgList
    toFArgs [] = []
    toFArgs (x :: xs) = x :: toFArgs xs

words' : List Char -> List (List Char)
words' s = case dropWhile isSpace s of
            [] => []
            s' => let (w, s'') = break isSpace s'
                  in w :: words' s''

export
words : String -> List String
words s = map pack (words' (unpack s))

lines' : List Char -> List (List Char)
lines' s = case dropWhile isNL s of
            [] => []
            s' => let (w, s'') = break isSpace s'
                  in w :: lines' s''

export
lines : String -> List String
lines s = map pack (lines' (unpack s))

export
ltrim : String -> String
ltrim xs = pack (ltrimChars (unpack xs))
  where
    ltrimChars : List Char -> List Char
    ltrimChars [] = []
    ltrimChars (x :: xs) = if isSpace x then ltrimChars xs else (x :: xs)

export
trim : String -> String
trim = ltrim . reverse . ltrim . reverse

||| Splits the string into a part before the predicate
||| returns False and the rest of the string.
|||
||| ```idris example
||| span (/= 'C') "ABCD"
||| ```
||| ```idris example
||| span (/= 'C') "EFGH"
||| ```
export
span : (Char -> Bool) -> String -> (String, String)
span p xs
    = case span p (unpack xs) of
           (x, y) => (pack x, pack y)

||| Splits the string into a part before the predicate
||| returns True and the rest of the string.
|||
||| ```idris example
||| break (== 'C') "ABCD"
||| ```
||| ```idris example
||| break (== 'C') "EFGH"
||| ```
public export
break : (Char -> Bool) -> String -> (String, String)
break p = span (not . p)


||| Splits the string into parts with the predicate
||| indicating separator characters.
|||
||| ```idris example
||| split (== '.') ".AB.C..D"
||| ```
public export
split : (Char -> Bool) -> String -> List String
split p xs = map pack (split p (unpack xs))

export
stringToNatOrZ : String -> Nat
stringToNatOrZ = fromInteger . prim__cast_StringInteger

export
toUpper : String -> String
toUpper str = pack (map toUpper (unpack str))

export
toLower : String -> String
toLower str = pack (map toLower (unpack str))
