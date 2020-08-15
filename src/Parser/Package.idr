module Parser.Package

import public Parser.Lexer.Package
import public Parser.Rules.Common
import public Parser.Rules.Package

import public Text.Lexer
import public Text.Parser

import Utils.Either

export
runPackageParser : String -> Grammar (TokenData PackageToken) e ty -> Either (ParsingError PackageToken) ty
runPackageParser str p
    = do toks   <- mapError LexFail       $ lexPackage str
         parsed <- mapError mapParseError $ parse p toks
         Right (fst parsed)

export
parsePackageFile : (filename : String) -> PackageRule ty -> IO (Either (ParsingError PackageToken) ty)
parsePackageFile filename p
    = do Right content <- readFile filename
             | Left error => pure (Left (FileFail error))
         pure (runPackageParser content p)
