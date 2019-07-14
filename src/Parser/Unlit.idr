module Parser.Unlit

%default total

export
isLitFile : String -> Bool
isLitFile file = isSuffixOf ".lidr" file

data LineType = Blank | Code | Text

lineType : String -> (LineType, String)
lineType str = if length str > 0
  then
    if assert_total (strHead str) == '>'
       then (Code, assert_total (strTail str))
       else
         if all isSpace (unpack str)
            then (Blank, str)
            else (Text, str)
  else (Blank, str)

export
isLit : String -> (Bool, String)
isLit str = case lineType str of
               (Code, tail) => (True, tail)
               _ => (False, str)

export
unlit : Bool -> Bool -> String -> Either (List Int) String
unlit lit enforce str = if lit
  then let (_, lns, errors) = foldr unlit' (Blank, [], []) (lines str) in
           if enforce
              then case errors of
                        [] => Right (unlines lns)
                        _ => let l : Int = cast (length lns) in Left (map (l -) errors)
              else Right (unlines lns)
  else Right str where
    unlit' : String -> (LineType, List String, List Int) -> (LineType, List String, List Int)
    unlit' str (type, ls, errs) with (lineType str)
      unlit' str (Code, ls, errs) | (Text, _) = (Text, "" :: ls, cast (length ls) :: errs)
      unlit' str (Text, ls, errs) | (Code, s) = (Code, (strCons ' ' s) :: ls, cast (length ls) :: errs)
      unlit' str (type, ls, errs) | (Code, s) = (Code, (strCons ' ' s) :: ls, errs)
      unlit' str (type, ls, errs) | (new, s) = (new, "" :: ls, errs)

