module Core.Name

%default total

public export
data Name : Type where
     NS : List String -> Name -> Name -- in a namespace
     UN : String -> Name -- user defined name
     MN : String -> Int -> Name -- machine generated name
     PV : Name -> Name -> Name -- pattern variable name
     MV : Int -> Name -- metavariable reference
     Nested : Name -> Name -> Name -- nested function name
     Resolved : Int -> Name -- resolved, index into context

export Show Name where
  show n = "[not done yet]"

export
showSep : String -> List String -> String
showSep sep [] = ""
showSep sep [x] = x
showSep sep (x :: xs) = x ++ sep ++ showSep sep xs

