module Parser.Rules.Package

import public Parser.Lexer.Package
import public Parser.Support
import public Text.Lexer
import public Text.Parser

public export
EmptyPackageRule : Type -> Type
EmptyPackageRule ty = Grammar (TokenData PackageToken) False ty

public export
PackageRule : Type -> Type
PackageRule ty = Grammar (TokenData PackageToken) True ty

export
eof : EmptyPackageRule ()
eof = do nextIs "Expected end of file" (isEOF . tok)
         pure ()
  where
    isEOF : PackageToken -> Bool
    isEOF EOF = True
    isEOF _   = False

export
assignment : PackageRule ()
assignment = terminal "Expected assignment symbol"
                      (\x => case tok x of
                                  Assignment => Just ()
                                  _ => Nothing)

export
property : String -> PackageRule ()
property p = terminal "Expected property name"
                    (\x => case tok x of
                                Property name => if name == p then Just ()
                                                 else Nothing
                                _ => Nothing)
export
string : PackageRule String
string = terminal "Expected a string literal"
                  (\x => case tok x of
                              StringLit str => Just str
                              _ => Nothing)
