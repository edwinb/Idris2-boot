module Parser.Lexer.Source

import public Text.Lexer

import Parser.Lexer.Common
import Utils.Hex
import Utils.Octal
import Utils.String

%default total

public export
data SourceToken
  -- Literals
  = CharLit    String
  | DoubleLit  Double
  | IntegerLit Integer
  | StringLit  String
  -- Identifiers
  | HoleIdent String
  | NSIdent   (List String)
  | Symbol    String
  -- Comments
  | Comment    String
  | DocComment String
  -- Special
  | CGDirective  String
  | EndInput
  | Keyword      String
  | Pragma       String
  | RecordField  String
  | Unrecognised String

export
Show SourceToken where
  -- Literals
  show (CharLit    c) = "character " ++ show c
  show (DoubleLit  d) = "double "    ++ show d
  show (IntegerLit n) = "integer "   ++ show n
  show (StringLit  s) = "string "    ++ s
  -- Identifiers
  show (HoleIdent i) = "hole identifier " ++ i
  show (NSIdent [i]) = "identifier "      ++ i
  show (NSIdent  ns) = "namespaced identifier " ++ dotSep ns
  show (Symbol    s) = "symbol " ++ s
  -- Comments
  show (Comment    c) = "comment"     ++ c
  show (DocComment c) = "doc comment" ++ c
  -- Special
  show (CGDirective  d) = "CGDirective " ++ d
  show EndInput         = "end of input"
  show (Keyword      k) = k
  show (Pragma       p) = "pragma " ++ p
  show (RecordField  f) = "record field " ++ f
  show (Unrecognised x) = "Unrecognised " ++ x

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

isIdentStart : Flavour -> Char -> Bool
isIdentStart _           '_' = True
isIdentStart Capitalised  x  = isUpper x || x > chr 160
isIdentStart _            x  = isAlpha x || x > chr 160

isIdentTrailing : Flavour -> Char -> Bool
isIdentTrailing AllowDashes '-'  = True
isIdentTrailing _           '\'' = True
isIdentTrailing _           '_'  = True
isIdentTrailing _            x   = isAlphaNum x || x > chr 160

%inline
isIdent : Flavour -> String -> Bool
isIdent flavour string =
  case unpack string of
    []      => False
    (x::xs) => isIdentStart flavour x && all (isIdentTrailing flavour) xs

%inline
ident : Flavour -> Lexer
ident flavour =
  (pred $ isIdentStart flavour) <+>
    (many . pred $ isIdentTrailing flavour)

export
isIdentNormal : String -> Bool
isIdentNormal = isIdent Normal

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

recField : Lexer
recField = is '.' <+> ident Normal

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

mkDirective : String -> SourceToken
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

fromOctLit : String -> Integer
fromOctLit str
  = if length str <= 2
       then 0
       else let num = assert_total (strTail (strTail str)) in
             case fromOct (reverse num) of
                  Nothing => 0 -- can't happen if the literal lexed correctly
                  Just n => cast n

rawTokens : TokenMap SourceToken
rawTokens =
    [(comment, Comment),
     (blockComment, Comment),
     (docComment, DocComment),
     (cgDirective, mkDirective),
     (holeIdent, \x => HoleIdent (assert_total (strTail x)))] ++
    map (\x => (exact x, Symbol)) symbols ++
    [(doubleLit, \x => DoubleLit (cast x)),
     (hexLit, \x => IntegerLit (fromHexLit x)),
     (octLit, \x => IntegerLit (fromOctLit x)),
     (digits, \x => IntegerLit (cast x)),
     (stringLit, \x => case isLTE 2 (length x) of
                            Yes prf => StringLit (stripQuotes x {ok=prf})
                            No  _   => Unrecognised x),
     (charLit, \x => case (isLTE 3 (length x) , isLTE 2 (length x)) of
                            (Yes _, Yes prf) => CharLit (stripQuotes x {ok=prf})
                            (_    , _      ) => Unrecognised x),
     (recField, \x => RecordField (assert_total $ strTail x)),
     (nsIdent, parseNSIdent),
     (ident Normal, parseIdent),
     (pragma, \x => Pragma (assert_total $ strTail x)),
     (space, Comment),
     (validSymbol, Symbol),
     (symbol, Unrecognised)]
  where
    parseNSIdent : String -> SourceToken
    parseNSIdent = NSIdent . reverse . split (== '.')

    parseIdent : String -> SourceToken
    parseIdent x =
      if x `elem` keywords
        then Keyword x
        else NSIdent [x]

export
lexTo : (TokenData SourceToken -> Bool) ->
        String -> Either (Int, Int, String) (List (TokenData SourceToken))
lexTo pred str
    = case lexTo pred rawTokens str of
           -- Add the EndInput token so that we'll have a line and column
           -- number to read when storing spans in the file
           (tok, (l, c, "")) => Right (filter notComment tok ++
                                      [MkToken l c EndInput])
           (_, fail) => Left fail
    where
      notComment : TokenData SourceToken -> Bool
      notComment t = case tok t of
                          Comment _ => False
                          DocComment _ => False -- TODO!
                          _ => True

export
lex : String -> Either (Int, Int, String) (List (TokenData SourceToken))
lex = lexTo (const False)
