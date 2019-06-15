module Data.List

public export
isNil : List a -> Bool
isNil []      = True
isNil (x::xs) = False

public export
isCons : List a -> Bool
isCons []      = False
isCons (x::xs) = True

public export
length : List a -> Nat
length []      = Z
length (x::xs) = S (length xs)

public export
take : Nat -> List a -> List a
take Z xs = []
take (S k) [] = []
take (S k) (x :: xs) = x :: take k xs

public export
drop : (n : Nat) -> (xs : List a) -> List a
drop Z     xs      = xs
drop (S n) []      = []
drop (S n) (x::xs) = drop n xs

public export
takeWhile : (p : a -> Bool) -> List a -> List a
takeWhile p []      = []
takeWhile p (x::xs) = if p x then x :: takeWhile p xs else []

public export
dropWhile : (p : a -> Bool) -> List a -> List a
dropWhile p []      = []
dropWhile p (x::xs) = if p x then dropWhile p xs else x::xs

public export
filter : (p : a -> Bool) -> List a -> List a
filter p [] = []
filter p (x :: xs) 
   = if p x
        then x :: filter p xs
        else filter p xs

public export
span : (a -> Bool) -> List a -> (List a, List a)
span p []      = ([], [])
span p (x::xs) =
  if p x then
    let (ys, zs) = span p xs in
      (x::ys, zs)
  else
    ([], x::xs)

public export
break : (a -> Bool) -> List a -> (List a, List a)
break p = span (not . p)

public export
split : (a -> Bool) -> List a -> List (List a)
split p xs =
  case break p xs of
    (chunk, [])          => [chunk]
    (chunk, (c :: rest)) => chunk :: split p rest

public export
splitAt : (n : Nat) -> (xs : List a) -> (List a, List a)
splitAt Z xs = ([], xs)
splitAt (S k) [] = ([], [])
splitAt (S k) (x :: xs) 
      = let (tk, dr) = splitAt k xs in
            (x :: tk, dr)

public export
partition : (a -> Bool) -> List a -> (List a, List a)
partition p []      = ([], [])
partition p (x::xs) =
  let (lefts, rights) = partition p xs in
    if p x then
      (x::lefts, rights)
    else
      (lefts, x::rights)

reverseOnto : List a -> List a -> List a
reverseOnto acc [] = acc
reverseOnto acc (x::xs) = reverseOnto (x::acc) xs

export
reverse : List a -> List a
reverse = reverseOnto []

public export
data NonEmpty : (xs : List a) -> Type where
    IsNonEmpty : NonEmpty (x :: xs)

export
Uninhabited (NonEmpty []) where
  uninhabited IsNonEmpty impossible
