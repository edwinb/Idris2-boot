module Idris.IDEMode.TokenLine

-- Tokenise a source line for easier processing

import Text.Lexer

public export
data SourcePart
  = Whitespace String
  | Name String
  | HoleName String
  | LBrace
  | RBrace
  | Equal
  | Other String

ident : Lexer
ident = pred startIdent <+> many (pred validIdent)
  where
    startIdent : Char -> Bool
    startIdent '_' = True
    startIdent x = isAlpha x

    validIdent : Char -> Bool
    validIdent '_' = True
    validIdent '\'' = True
    validIdent x = isAlphaNum x

holeIdent : Lexer
holeIdent = is '?' <+> ident

srcTokens : TokenMap SourcePart
srcTokens = 
    [(ident, Name),
     (holeIdent, \x => HoleName (assert_total (strTail x))),
     (space, Whitespace),
     (is '{', const LBrace),
     (is '}', const RBrace),
     (is '=', const Equal),
     (any, Other)]

export
tokens : String -> List SourcePart
tokens str 
    = case lex srcTokens str of
           -- Add the EndInput token so that we'll have a line and column
           -- number to read when storing spans in the file
           (srctoks, (l, c, rest)) => 
              map tok srctoks ++ (if rest == "" then [] else [Other rest])

