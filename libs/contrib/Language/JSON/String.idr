module Language.JSON.String

import Language.JSON.String.Lexer
import Language.JSON.String.Parser
import Language.JSON.String.Tokens
import Text.Lexer

%default total

export
permissiveStringLit : Lexer
permissiveStringLit
  = quo <+> manyUntil quo (esc any <|> any) <+> opt quo

export
stringValue : String -> Maybe String
stringValue x = parseString !(lexString x)
