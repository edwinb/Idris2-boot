0 notE : Bool -> Bool
notE b = case b of
	True => False
	False => True

1 notL : Bool -> Bool
notL b = case b of
	True => False
	False => True

notR : Bool -> Bool
notR b = case b of
	True => False
	False => True

0 eqE : (0 eq : True = True) -> Bool
eqE eq = case eq of
	Refl => True

{-
1 eqL : (0 eq : True = True) -> Bool
eqL eq = case eq of
	Refl => True

eqR : (0 eq : True = True) -> Bool
eqR eq = case eq of
	Refl => True
-}
