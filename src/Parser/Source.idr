module Parser.Source

import public Parser.Lexer.Source
import public Parser.Rules.Source
import public Parser.Support

import public Text.Lexer
import public Text.Literate
import public Text.Parser

import Utils.Either

export
runSourceParserTo : Maybe LiterateStyle -> (TokenData SourceToken -> Bool) ->
              String -> Grammar (TokenData SourceToken) e ty -> Either (ParsingError SourceToken) ty
runSourceParserTo lit pred str p
    = do str    <- mapError LitFail       $ unlit lit str
         toks   <- mapError LexFail       $ lexTo pred str
         parsed <- mapError mapParseError $ parse p toks
         Right (fst parsed)

export
runSourceParser : Maybe LiterateStyle -> String -> Grammar (TokenData SourceToken) e ty -> Either (ParsingError SourceToken) ty
runSourceParser lit = runSourceParserTo lit (const False)

export
parseSourceFile : (filename : String) -> SourceRule ty -> IO (Either (ParsingError SourceToken) ty)
parseSourceFile filename p
    = do Right content <- readFile filename
             | Left error => pure (Left (FileFail error))
         pure (runSourceParser (isLitFile filename) content p)
