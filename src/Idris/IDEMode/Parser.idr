||| Slightly different lexer than the source language because we are more free
||| as to what can be identifiers, and fewer tokens are supported. But otherwise,
||| we can reuse the standard stuff
module Idris.IDEMode.Parser

import Idris.IDEMode.Commands

import Text.Parser
import Parser.Lexer.Source
import Parser.Support
import Text.Lexer
import Utils.Either
import Utils.String

%hide Lexer.Source.symbols

ideTokens : TokenMap SourceToken
ideTokens =
    map (\x => (exact x, Symbol)) symbols ++
    [(digits, \x => IntegerLit (cast x)),
     (stringLit, \x => case (isLTE 2 $ length x) of
                            Yes prf => StringLit (stripQuotes x)
                            No  _   => Unrecognised x),
     (identAllowDashes, \x => NSIdent [x]),
     (space, Comment)]
  where
    symbols : List String
    symbols = ["(", ":", ")"]

idelex : String -> Either (Int, Int, String) (List (TokenData SourceToken))
idelex str
    = case lex ideTokens str of
           -- Add the EndInput token so that we'll have a line and column
           -- number to read when storing spans in the file
           (tok, (l, c, "")) => Right (filter notComment tok ++
                                      [MkToken l c EndInput])
           (_, fail) => Left fail
    where
      notComment : TokenData SourceToken -> Bool
      notComment t = case tok t of
                          Comment _ => False
                          _ => True

sexp : Rule SExp
sexp
    = do symbol ":"; exactIdent "True"
         pure (BoolAtom True)
  <|> do symbol ":"; exactIdent "False"
         pure (BoolAtom False)
  <|> do i <- intLit
         pure (IntegerAtom i)
  <|> do str <- strLit
         pure (StringAtom str)
  <|> do symbol ":"; x <- unqualifiedName
         pure (SymbolAtom x)
  <|> do symbol "("
         xs <- many sexp
         symbol ")"
         pure (SExpList xs)

ideParser : String -> Grammar (TokenData SourceToken) e ty -> Either ParseError ty
ideParser str p
    = do toks   <- mapError LexFail $ idelex str
         parsed <- mapError mapParseError $ parse p toks
         Right (fst parsed)

export
parseSExp : String -> Either ParseError SExp
parseSExp inp
    = ideParser inp (do c <- sexp; eoi; pure c)
