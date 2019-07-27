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

||| Compute the intersect of two lists by user-supplied equality predicate.
export
intersectBy : (a -> a -> Bool) -> List a -> List a -> List a
intersectBy eq xs ys = [x | x <- xs, any (eq x) ys]

||| Compute the intersect of two lists according to the `Eq` implementation for the elements.
export
intersect : Eq a => List a -> List a -> List a
intersect = intersectBy (==)

public export
data NonEmpty : (xs : List a) -> Type where
    IsNonEmpty : NonEmpty (x :: xs)

export
Uninhabited (NonEmpty []) where
  uninhabited IsNonEmpty impossible

||| Convert any Foldable structure to a list.
export
toList : Foldable t => t a -> List a
toList = foldr (::) []

--------------------------------------------------------------------------------
-- Sorting
--------------------------------------------------------------------------------

||| Check whether a list is sorted with respect to the default ordering for the type of its elements.
export
sorted : Ord a => List a -> Bool
sorted []      = True
sorted (x::xs) =
  case xs of
    Nil     => True
    (y::ys) => x <= y && sorted (y::ys)

||| Merge two sorted lists using an arbitrary comparison
||| predicate. Note that the lists must have been sorted using this
||| predicate already.
export
mergeBy : (a -> a -> Ordering) -> List a -> List a -> List a
mergeBy order []      right   = right
mergeBy order left    []      = left
mergeBy order (x::xs) (y::ys) =
  case order x y of
       LT => x :: mergeBy order xs (y::ys)
       _  => y :: mergeBy order (x::xs) ys

||| Merge two sorted lists using the default ordering for the type of their elements.
export
merge : Ord a => List a -> List a -> List a
merge = mergeBy compare

||| Sort a list using some arbitrary comparison predicate.
|||
||| @ cmp how to compare elements
||| @ xs the list to sort
export
sortBy : (cmp : a -> a -> Ordering) -> (xs : List a) -> List a
sortBy cmp []  = []
sortBy cmp [x] = [x]
sortBy cmp xs  = let (x, y) = split xs in
    mergeBy cmp
          (sortBy cmp (assert_smaller xs x))
          (sortBy cmp (assert_smaller xs y)) -- not structurally smaller, hence assert
  where
    splitRec : List a -> List a -> (List a -> List a) -> (List a, List a)
    splitRec (_::_::xs) (y::ys) zs = splitRec xs ys (zs . ((::) y))
    splitRec _          ys      zs = (zs [], ys)

    split : List a -> (List a, List a)
    split xs = splitRec xs xs id

||| Sort a list using the default ordering for the type of its elements.
export
sort : Ord a => List a -> List a
sort = sortBy compare

--------------------------------------------------------------------------------
-- Properties
--------------------------------------------------------------------------------

export
Uninhabited ([] = Prelude.(::) x xs) where
  uninhabited Refl impossible

export
Uninhabited (Prelude.(::) x xs = []) where
  uninhabited Refl impossible
-- 
-- ||| (::) is injective
-- consInjective : {x : a} -> {xs : List a} -> {y : b} -> {ys : List b} ->
--                 (x :: xs) = (y :: ys) -> (x = y, xs = ys)
-- consInjective Refl = (Refl, Refl)
-- 
-- ||| Two lists are equal, if their heads are equal and their tails are equal.
-- consCong2 : {x : a} -> {xs : List a} -> {y : b} -> {ys : List b} ->
--             x = y -> xs = ys -> x :: xs = y :: ys
-- consCong2 Refl Refl = Refl
-- 
-- ||| Appending pairwise equal lists gives equal lists
-- appendCong2 : {x1 : List a} -> {x2 : List a} ->
--               {y1 : List b} -> {y2 : List b} ->
--               x1 = y1 -> x2 = y2 -> x1 ++ x2 = y1 ++ y2
-- appendCong2 {x1=[]} {y1=(_ :: _)} Refl _ impossible
-- appendCong2 {x1=(_ :: _)} {y1=[]} Refl _ impossible
-- appendCong2 {x1=[]} {y1=[]} _ eq2 = eq2
-- appendCong2 {x1=(_ :: _)} {y1=(_ :: _)} eq1 eq2 =
--   consCong2
--     (fst $ consInjective eq1)
--     (appendCong2 (snd $ consInjective eq1) eq2)
-- 
-- ||| List.map is distributive over appending.
-- mapAppendDistributive : (f : a -> b) -> (x : List a) -> (y : List a) ->
--                         map f (x ++ y) = map f x ++ map f y
-- mapAppendDistributive _ [] _ = Refl
-- mapAppendDistributive f (_ :: xs) y = cong $ mapAppendDistributive f xs y
-- 
||| The empty list is a right identity for append.
export
appendNilRightNeutral : (l : List a) ->
  l ++ [] = l
appendNilRightNeutral []      = Refl
appendNilRightNeutral (x::xs) =
  let inductiveHypothesis = appendNilRightNeutral xs in
    rewrite inductiveHypothesis in Refl

||| Appending lists is associative.
export
appendAssociative : (l : List a) -> (c : List a) -> (r : List a) ->
  l ++ (c ++ r) = (l ++ c) ++ r
appendAssociative []      c r = Refl
appendAssociative (x::xs) c r =
  let inductiveHypothesis = appendAssociative xs c r in
    rewrite inductiveHypothesis in Refl
