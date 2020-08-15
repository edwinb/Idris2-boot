module Parser.CommonLexer

%default total

export
dotSep : List String -> String
dotSep []  = ""
dotSep [x] = x
dotSep l@(_::_)
  = assert_total $ let rl@(_::_) = reverse l in
    head rl ++ concat ["." ++ y | y <- tail rl]
