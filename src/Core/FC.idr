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

-- Return whether a given file position is within the file context (assuming we're
-- in the right file)
export
within : FilePos -> FC -> Bool
within (x, y) (MkFC _ start end)
   = (x, y) >= start && (x, y) <= end

-- Return whether a given line is on the same line as the file context (assuming 
-- we're in the right file)
export
onLine : Int -> FC -> Bool
onLine x (MkFC _ start end)
   = x >= fst start && x <= fst end

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


