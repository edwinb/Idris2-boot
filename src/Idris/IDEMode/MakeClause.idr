module Idris.IDEMode.MakeClause

import Core.Name
import Parser.Lexer

-- Implement make-with and make-case from the IDE mode

isLit : String -> (Bool, String)
isLit str 
    = assert_total $
         if length str > 0 && strHead str == '>'
            then (True, strTail str)
            else (False, str)

showRHSName : Name -> String
showRHSName n
    = let fn = show (dropNS n) in
          if any (flip elem (unpack opChars)) (unpack fn)
             then "op"
             else fn

export
makeWith : Name -> String -> String
makeWith n srcline
    = let (lit, src) = isLit srcline
          isrc : (Nat, String) =
             case span isSpace src of
                  (spc, rest) => (length spc, rest)
          indent = fst isrc
          src = snd isrc 
          lhs = pack (readLHS 0 (unpack src)) in
          mkWithArg lit indent lhs ++ "\n" ++
          mkWithPat lit indent lhs ++ "\n"
  where
    readLHS : (brackets : Nat) -> List Char -> List Char
    readLHS Z ('=' :: rest) = []
    readLHS n ('(' :: rest) = '(' :: readLHS (S n) rest
    readLHS n ('{' :: rest) = '{' :: readLHS (S n) rest
    readLHS n (')' :: rest) = ')' :: readLHS (pred n) rest
    readLHS n ('}' :: rest) = '}' :: readLHS (pred n) rest
    readLHS n (x :: rest) = x :: readLHS n rest
    readLHS n [] = []

    pref : Bool -> Nat -> String
    pref l ind
        = (if l then ">" else "") ++ 
          pack (replicate ind ' ')

    mkWithArg : Bool -> Nat -> String -> String
    mkWithArg lit indent lhs 
        = pref lit indent ++ lhs ++ "with (_)"

    mkWithPat : Bool -> Nat -> String -> String
    mkWithPat lit indent lhs 
        = pref lit (indent + 2) ++ lhs ++ "| with_pat = ?" ++ 
              showRHSName n ++ "_rhs"

