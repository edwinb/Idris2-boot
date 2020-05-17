module Parser.Rules.Common

import Text.Lexer
import Text.Parser

public export
EmptyRule : Type -> Type -> Type
EmptyRule token ty = Grammar (TokenData token) False ty

export
location : {token : Type} -> EmptyRule token (Int, Int)
location
    = do tok <- peek
         pure (line tok, col tok)

export
column : {token : Type} -> EmptyRule token Int
column
    = do (line, col) <- location
         pure col
