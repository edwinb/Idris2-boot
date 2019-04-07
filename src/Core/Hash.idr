module Core.Hash

import Core.TT
import Data.List

%default total

-- This is so that we can store a hash of the interface in ttc files, to avoid
-- the need for reloading modules when no interfaces have changed in imports.
-- As you can probably tell, I know almost nothing about writing good hash
-- functions, so better implementations will be very welcome...

public export
interface Hashable a where
  hash : a -> Int
  hashWithSalt : Int -> a -> Int
  
  hash = hashWithSalt 5381
  hashWithSalt h i = h * 33 + hash i

export
Hashable Int where
  hash = id

export
Hashable Char where
  hash = cast

export
Hashable a => Hashable (List a) where
  hashWithSalt h [] = abs h
  hashWithSalt h (x :: xs) = hashWithSalt (h * 33 + hash x) xs

export
Hashable String where
  hashWithSalt h str = hashChars h 0 (cast (length str)) str
    where
      hashChars : Int -> Int -> Int -> String -> Int
      hashChars h p len str
          = assert_total $
              if p == len 
                 then h
                 else hashChars (h * 33 + cast (strIndex str p)) 
                                (p + 1) len str

export
Hashable Name where
  hashWithSalt h (MN s _) = hashWithSalt h s
  hashWithSalt h n = hashWithSalt h (show n)

count : RigCount -> String
count Rig0 = "0"
count Rig1 = "1"
count RigW = "w"

plicity : PiInfo -> String
plicity Implicit = "{}"
plicity Explicit = "()"
plicity AutoImplicit = "{a}"

-- I suppose this'll do for now... TODO: Write a proper one!
-- Converting to a string (and indeed, however we do the hash function...)
-- we need to ignore machine generated names because they'll have different
-- numbers depending on implementations of functions, and that doesn't affect
-- the exported interface.
hshow : Term vars -> String
-- hshow (Local {x} _ _) = nameRoot x
-- hshow (Ref _ n) = nameRoot n
-- hshow (Bind x (Lam c p ty) sc) 
--    = "\\" ++ nameRoot x ++ count c ++ plicity p ++ hshow ty ++ "." ++ hshow sc
-- hshow (Bind x (Let c val ty) sc) 
--    = "let " ++ nameRoot x ++ count c ++ " " ++ hshow val ++ " " ++ hshow ty ++ "."
--             ++ hshow sc
-- hshow (Bind x (Pi c p ty) sc) 
--    = "pi." ++ nameRoot x ++ count c ++ plicity p ++ hshow ty ++ "." ++ hshow sc
-- hshow (Bind x (PVar c ty) sc)
--    = "pvar." ++ nameRoot x ++ count c ++ hshow ty ++ "." ++ hshow sc
-- hshow (Bind x (PLet c val ty) sc)
--    = "plet " ++ nameRoot x ++ count c ++ " " ++ hshow val ++ " " ++ hshow ty ++ "."
--              ++ hshow sc
-- hshow (Bind x (PVTy c ty) sc)
--    = "pty." ++ nameRoot x ++ count c ++ hshow ty ++ "." ++ hshow sc
-- hshow (App f a) = "(" ++ hshow f ++ " " ++ hshow a ++ ")"
-- hshow (PrimVal x) = show x
-- hshow TType = "#"
-- hshow Erased = "_"

export
Hashable (Term vars) where
  hashWithSalt h tm 
     = hashWithSalt h (hshow tm)

