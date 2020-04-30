module Parser.Lexer

import public Text.Lexer
import Utils.Hex

%default total

public export
data Token = NSIdent (List String)
           | HoleIdent String
           | Literal Integer
           | StrLit String
           | CharLit String
           | DoubleLit Double
           | Symbol String
           | Keyword String
           | Unrecognised String
           | Comment String
           | DocComment String
           | CGDirective String
           | DotIdent String
           | Pragma String
           | EndInput

export
Show Token where
  show (HoleIdent x) = "hole identifier " ++ x
  show (Literal x) = "literal " ++ show x
  show (StrLit x) = "string " ++ show x
  show (CharLit x) = "character " ++ show x
  show (DoubleLit x) = "double " ++ show x
  show (Symbol x) = "symbol " ++ x
  show (Keyword x) = x
  show (Unrecognised x) = "Unrecognised " ++ x
  show (Comment _) = "comment"
  show (DocComment _) = "doc comment"
  show (CGDirective x) = "CGDirective " ++ x
  show (DotIdent x) = "record field " ++ x
  show (Pragma x) = "pragma " ++ x
  show EndInput = "end of input"
  show (NSIdent [x]) = "identifier " ++ x
  show (NSIdent xs) = "namespaced identifier " ++ dotSep (reverse xs)
    where
      dotSep : List String -> String
      dotSep [] = ""
      dotSep [x] = x
      dotSep (x :: xs) = x ++ concat ["." ++ y | y <- xs]

export
Show (TokenData Token) where
  show t = show (line t, col t, tok t)

||| In `comment` we are careful not to parse closing delimiters as
||| valid comments. i.e. you may not write many dashes followed by
||| a closing brace and call it a valid comment.
comment : Lexer
comment
   =  is '-' <+> is '-'                  -- comment opener
  <+> many (is '-') <+> reject (is '}')  -- not a closing delimiter
  <+> many (isNot '\n')                  -- till the end of line

mutual

  ||| The mutually defined functions represent different states in a
  ||| small automaton.
  ||| `toEndComment` is the default state and it will munch through
  ||| the input until we detect a special character (a dash, an
  ||| opening brace, or a double quote) and then switch to the
  ||| appropriate state.
  toEndComment : (k : Nat) -> Recognise (k /= 0)
  toEndComment Z = empty
  toEndComment (S k)
               = some (pred (\c => c /= '-' && c /= '{' && c /= '"'))
                        <+> toEndComment (S k)
             <|> is '{' <+> singleBrace k
             <|> is '-' <+> singleDash k
             <|> stringLit <+> toEndComment (S k)

  ||| After reading a single brace, we may either finish reading an
  ||| opening delimiter or ignore it (e.g. it could be an implicit
  ||| binder).
  singleBrace : (k : Nat) -> Lexer
  singleBrace k
     =  is '-' <+> many (is '-')    -- opening delimiter
               <+> singleDash (S k) -- handles the {----} special case
    <|> toEndComment (S k)          -- not a valid comment

  ||| After reading a single dash, we may either find another one,
  ||| meaning we may have started reading a line comment, or find
  ||| a closing brace meaning we have found a closing delimiter.
  singleDash : (k : Nat) -> Lexer
  singleDash k
     =  is '-' <+> doubleDash k    -- comment or closing delimiter
    <|> is '}' <+> toEndComment k  -- closing delimiter
    <|> toEndComment (S k)         -- not a valid comment

  ||| After reading a double dash, we are potentially reading a line
  ||| comment unless the series of uninterrupted dashes is ended with
  ||| a closing brace in which case it is a closing delimiter.
  doubleDash : (k : Nat) -> Lexer
  doubleDash k = many (is '-') <+> choice      -- absorb all dashes
    [ is '}' <+> toEndComment k                -- closing delimiter
    , many (isNot '\n') <+> toEndComment (S k) -- line comment
    ]

blockComment : Lexer
blockComment = is '{' <+> is '-' <+> toEndComment 1

docComment : Lexer
docComment = is '|' <+> is '|' <+> is '|' <+> many (isNot '\n')

-- Identifier Lexer
-- There are multiple variants.

data Flavour = Capitalised | AllowDashes | Normal

startIdent : Flavour -> Char -> Bool
startIdent Capitalised x = isUpper x
startIdent _ '_' = True
startIdent _  x  = isAlpha x || x > chr 127

%inline
validIdent' : Flavour -> Char -> Bool
validIdent' _ '_'  = True
validIdent' AllowDashes '-'  = True
validIdent' _ '-'  = False
validIdent' _ '\'' = True
validIdent' _  x   = isAlphaNum x || x > chr 127

%inline
ident : Flavour -> Lexer
ident flavour =
  (pred $ startIdent flavour) <+>
    (many . pred $ validIdent' flavour)

export
identNormal : Lexer
identNormal = ident Normal

export
identAllowDashes : Lexer
identAllowDashes = ident AllowDashes

holeIdent : Lexer
holeIdent = is '?' <+> ident Normal

nsIdent : Lexer
nsIdent = ident Capitalised <+> many (is '.' <+> ident Normal)

dotIdent : Lexer
dotIdent = is '.' <+> ident Normal

pragma : Lexer
pragma = is '%' <+> ident Normal

doubleLit : Lexer
doubleLit
    = digits <+> is '.' <+> digits <+> opt
           (is 'e' <+> opt (is '-' <|> is '+') <+> digits)

-- Do this as an entire token, because the contents will be processed by
-- a specific back end
cgDirective : Lexer
cgDirective
    = exact "%cg" <+>
      ((some space <+>
           some (pred isAlphaNum) <+> many space <+>
           is '{' <+> many (isNot '}') <+>
           is '}')
         <|> many (isNot '\n'))

mkDirective : String -> Token
mkDirective str = CGDirective (trim (substr 3 (length str) str))

-- Reserved words
keywords : List String
keywords = ["data", "module", "where", "let", "in", "do", "record",
            "auto", "default", "implicit", "mutual", "namespace",
            "parameters", "with", "impossible", "case", "of",
            "if", "then", "else", "forall", "rewrite",
            "using", "interface", "implementation", "open", "import",
            "public", "export", "private",
            "infixl", "infixr", "infix", "prefix",
            "total", "partial", "covering"]

-- Reserved words for internal syntax
special : List String
special = ["%lam", "%pi", "%imppi", "%let"]

-- Special symbols - things which can't be a prefix of another symbol, and
-- don't match 'validSymbol'
export
symbols : List String
symbols
    = [".(", -- for things such as Foo.Bar.(+)
       "@{",
       "[|", "|]",
       "(", ")", "{", "}", "[", "]", ",", ";", "_",
       "`(", "`"]


export
isOpChar : Char -> Bool
isOpChar c = c `elem` (unpack ":!#$%&*+./<=>?@\\^|-~")

validSymbol : Lexer
validSymbol = some (pred isOpChar)

-- Valid symbols which have a special meaning so can't be operators
export
reservedSymbols : List String
reservedSymbols
    = symbols ++
      ["%", "\\", ":", "=", "|", "|||", "<-", "->", "=>", "?", "!",
       "&", "**", ".."]

fromHexLit : String -> Integer
fromHexLit str
  = if length str <= 2
       then 0
       else let num = assert_total (strTail (strTail str)) in
             case fromHex (reverse num) of
                  Nothing => 0 -- can't happen if the literal lexed correctly
                  Just n => cast n

rawTokens : TokenMap Token
rawTokens =
    [(comment, Comment),
     (blockComment, Comment),
     (docComment, DocComment),
     (cgDirective, mkDirective),
     (holeIdent, \x => HoleIdent (assert_total (strTail x)))] ++
    map (\x => (exact x, Symbol)) symbols ++
    [(doubleLit, \x => DoubleLit (cast x)),
     (hexLit, \x => Literal (fromHexLit x)),
     (digits, \x => Literal (cast x)),
     (stringLit, \x => StrLit (stripQuotes x)),
     (charLit, \x => CharLit (stripQuotes x)),
     (dotIdent, \x => DotIdent (assert_total $ strTail x)),
     (nsIdent, parseNSIdent),
     (ident Normal, parseIdent),
     (pragma, \x => Pragma (assert_total $ strTail x)),
     (space, Comment),
     (validSymbol, Symbol),
     (symbol, Unrecognised)]
  where
    stripQuotes : String -> String
    -- ASSUMPTION! Only total because we know we're getting quoted strings.
    stripQuotes = assert_total (strTail . reverse . strTail . reverse)

    parseNSIdent : String -> Token
    parseNSIdent = NSIdent . reverse . split (== '.')

    parseIdent : String -> Token
    parseIdent x =
      if x `elem` keywords
        then Keyword x
        else NSIdent [x]

export
lexTo : (TokenData Token -> Bool) ->
        String -> Either (Int, Int, String) (List (TokenData Token))
lexTo pred str
    = case lexTo pred rawTokens str of
           -- Add the EndInput token so that we'll have a line and column
           -- number to read when storing spans in the file
           (tok, (l, c, "")) => Right (filter notComment tok ++
                                      [MkToken l c EndInput])
           (_, fail) => Left fail
    where
      notComment : TokenData Token -> Bool
      notComment t = case tok t of
                          Comment _ => False
                          DocComment _ => False -- TODO!
                          _ => True

export
lex : String -> Either (Int, Int, String) (List (TokenData Token))
lex = lexTo (const False)
