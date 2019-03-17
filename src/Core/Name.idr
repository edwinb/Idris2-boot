module Core.Name

%default total

public export
data Name : Type where
     NS : List String -> Name -> Name -- in a namespace
     UN : String -> Name -- user defined name
     MN : String -> Int -> Name -- machine generated name
     PV : Name -> Name -> Name -- pattern variable name
     Nested : Name -> Name -> Name -- nested function name
     Resolved : Int -> Name -- resolved, index into context

export
userNameRoot : Name -> Maybe String
userNameRoot (NS _ n) = userNameRoot n
userNameRoot (UN n) = Just n
userNameRoot _ = Nothing

export
showSep : String -> List String -> String
showSep sep [] = ""
showSep sep [x] = x
showSep sep (x :: xs) = x ++ sep ++ showSep sep xs

export Show Name where
  show (NS ns n) = showSep "." (reverse ns) ++ "." ++ show n
  show (UN x) = x
  show (MN x y) = "{" ++ x ++ ":" ++ show y ++ "}"
  show (PV n d) = "{P:" ++ show n ++ ":" ++ show d ++ "}"
  show (Nested outer inner) = show outer ++ ":" ++ show inner
  show (Resolved x) = "$resolved" ++ show x

export
Eq Name where
    (==) (NS ns n) (NS ns' n') = ns == ns' && n == n'
    (==) (UN x) (UN y) = x == y
    (==) (MN x y) (MN x' y') = y == y' && x == x'
    (==) (PV x y) (PV x' y') = x == x' && y == y'
    (==) (Nested x y) (Nested x' y') = x == x' && y == y'
    (==) (Resolved x) (Resolved x') = x == x'
    (==) _ _ = False

nameTag : Name -> Int
nameTag (NS _ _) = 0
nameTag (UN _) = 1
nameTag (MN _ _) = 2
nameTag (PV _ _) = 3
nameTag (Nested _ _) = 4
nameTag (Resolved _) = 5

export
Ord Name where
    compare (NS x y) (NS x' y') 
        = case compare y y' of -- Compare base name first (more likely to differ)
               EQ => compare x x'
               -- Because of the terrible way Idris 1 compiles 'case', this
               -- is actually faster than just having 't => t'...
               GT => GT
               LT => LT
    compare (UN x) (UN y) = compare x y
    compare (MN x y) (MN x' y') 
        = case compare y y' of
               EQ => compare x x'
               GT => GT
               LT => LT
    compare (PV x y) (PV x' y')
        = case compare y y' of
               EQ => compare x x'
               GT => GT
               LT => LT
    compare (Nested x y) (Nested x' y')
        = case compare y y' of
               EQ => compare x x'
               GT => GT
               LT => LT
    compare (Resolved x) (Resolved y) = compare x y

    compare x y = compare (nameTag x) (nameTag y)

export
nameEq : (x : Name) -> (y : Name) -> Maybe (x = y)
nameEq (NS xs x) (NS ys y) with (decEq xs ys)
  nameEq (NS ys x) (NS ys y) | (Yes Refl) with (nameEq x y)
    nameEq (NS ys x) (NS ys y) | (Yes Refl) | Nothing = Nothing
    nameEq (NS ys y) (NS ys y) | (Yes Refl) | (Just Refl) = Just Refl
  nameEq (NS xs x) (NS ys y) | (No contra) = Nothing
nameEq (UN x) (UN y) with (decEq x y)
  nameEq (UN y) (UN y) | (Yes Refl) = Just Refl
  nameEq (UN x) (UN y) | (No contra) = Nothing
nameEq (MN x t) (MN x' t') with (decEq x x')
  nameEq (MN x t) (MN x t') | (Yes Refl) with (decEq t t')
    nameEq (MN x t) (MN x t) | (Yes Refl) | (Yes Refl) = Just Refl
    nameEq (MN x t) (MN x t') | (Yes Refl) | (No contra) = Nothing
  nameEq (MN x t) (MN x' t') | (No contra) = Nothing
nameEq (PV x t) (PV y t') with (nameEq x y)
  nameEq (PV y t) (PV y t') | (Just Refl) with (nameEq t t')
    nameEq (PV y t) (PV y t) | (Just Refl) | (Just Refl) = Just Refl
    nameEq (PV y t) (PV y t') | (Just Refl) | Nothing = Nothing
  nameEq (PV x t) (PV y t') | Nothing = Nothing
nameEq (Nested x y) (Nested x' y') with (nameEq x x')
  nameEq (Nested x y) (Nested x' y') | Nothing = Nothing
  nameEq (Nested x y) (Nested x y') | (Just Refl) with (nameEq y y')
    nameEq (Nested x y) (Nested x y') | (Just Refl) | Nothing = Nothing
    nameEq (Nested x y) (Nested x y) | (Just Refl) | (Just Refl) = Just Refl
nameEq (Resolved x) (Resolved y) with (decEq x y)
  nameEq (Resolved y) (Resolved y) | (Yes Refl) = Just Refl
  nameEq (Resolved x) (Resolved y) | (No contra) = Nothing
nameEq _ _ = Nothing 

