module Data.Strings

import Data.List

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
