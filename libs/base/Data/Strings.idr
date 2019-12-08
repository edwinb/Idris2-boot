module Data.Strings

import Data.List

partial
foldr1 : (a -> a -> a) -> List a -> a
foldr1 _ [x] = x
foldr1 f (x::xs) = f x (foldr1 f xs)

partial
foldl1 : (a -> a -> a) -> List a -> a
foldl1 f (x::xs) = foldl f x xs

-- This works quickly because when string-append builds the result, it allocates
-- enough room in advance so there's only one allocation, rather than lots!
export
fastAppend : List String -> String
fastAppend xs = unsafePerformIO (schemeCall String "string-append" (toFArgs xs))
  where
    toFArgs : List String -> FArgList
    toFArgs [] = []
    toFArgs (x :: xs) = x :: toFArgs xs

||| Splits a character list into a list of whitespace separated character lists.
|||
||| ```idris example
||| words' (unpack " A B C  D E   ")
||| ```
words' : List Char -> List (List Char)
words' s = case dropWhile isSpace s of
            [] => []
            s' => let (w, s'') = break isSpace s'
                  in w :: words' s''

||| Splits a string into a list of whitespace separated strings.
|||
||| ```idris example
||| words " A B C  D E   "
||| ```
export
words : String -> List String
words s = map pack (words' (unpack s))

||| Joins the character lists by spaces into a single character list.
|||
||| ```idris example
||| unwords' [['A'], ['B', 'C'], ['D'], ['E']]
||| ```
unwords' : List (List Char) -> List Char
unwords' [] = []
unwords' ws = assert_total (foldr1 addSpace ws) where
  addSpace : List Char -> List Char -> List Char
  addSpace w s = w ++ (' ' :: s)

||| Joins the strings by spaces into a single string.
|||
||| ```idris example
||| unwords ["A", "BC", "D", "E"]
||| ```
export
unwords : List String -> String
unwords = pack . unwords' . map unpack

||| Splits a character list into a list of newline separated character lists.
|||
||| ```idris example
||| lines' (unpack "\rA BC\nD\r\nE\n")
||| ```
lines' : List Char -> List (List Char)
lines' s = case dropWhile isNL s of
            [] => []
            s' => let (w, s'') = break isNL s'
                  in w :: lines' s''

||| Splits a string into a list of newline separated strings.
|||
||| ```idris example
||| lines  "\rA BC\nD\r\nE\n"
||| ```
export
lines : String -> List String
lines s = map pack (lines' (unpack s))

||| Joins the character lists by newlines into a single character list.
|||
||| ```idris example
||| unlines' [['l','i','n','e'], ['l','i','n','e','2'], ['l','n','3'], ['D']]
||| ```
unlines' : List (List Char) -> List Char
unlines' [] = []
unlines' (l::ls) = l ++ '\n' :: unlines' ls

||| Joins the strings by newlines into a single string.
|||
||| ```idris example
||| unlines ["line", "line2", "ln3", "D"]
||| ```
export
unlines : List String -> String
unlines = pack . unlines' . map unpack

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
