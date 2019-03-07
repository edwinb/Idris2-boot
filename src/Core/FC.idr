module Core.FC

public export
FilePos : Type
FilePos = (Int, Int)

showPos : FilePos -> String
showPos (l, c) = show (l + 1) ++ ":" ++ show (c + 1)

public export
FileName : Type
FileName = String

public export
record FC where
  constructor MkFC
  file : FileName
  startPos : FilePos
  endPos : FilePos

export
emptyFC : FC
emptyFC = MkFC "(no file)" (0, 0) (0, 0)

export
toplevelFC : FC
toplevelFC = MkFC "(toplevel)" (0, 0) (0, 0)

%name FC fc

export
Show FC where
  show loc = file loc ++ ":" ++ 
             showPos (startPos loc) ++ "--" ++ 
             showPos (endPos loc)


