module Data.Maybe

public export
isNothing : Maybe a -> Bool
isNothing Nothing  = True
isNothing (Just j) = False

public export
isJust : Maybe a -> Bool
isJust Nothing  = False
isJust (Just j) = True

||| Proof that some `Maybe` is actually `Just`
public export
data IsJust : Maybe a -> Type where
  ItIsJust : IsJust (Just x)

export
Uninhabited (IsJust Nothing) where
  uninhabited ItIsJust impossible

||| Decide whether a 'Maybe' is 'Just'
public export
isItJust : (v : Maybe a) -> Dec (IsJust v)
isItJust (Just x) = Yes ItIsJust
isItJust Nothing = No absurd

