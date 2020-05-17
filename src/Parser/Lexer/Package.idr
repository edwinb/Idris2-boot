module Parser.Lexer.Package

import public Text.Lexer

%default total

public export
data PackageToken
  = Assignment
  | Comment
  | EOF
  | PackageName String
  | Property String
  | Module (List String)
  | StringLit String

export
lexPackage : String -> Either (Int, Int, String) (List (TokenData PackageToken))
