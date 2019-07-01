module Data.Vect

import Data.List
import Data.Nat
import public Data.Fin

public export
data Vect : (len : Nat) -> (elem : Type) -> Type where
  ||| Empty vector
  Nil  : Vect Z elem
  ||| A non-empty vector of length `S len`, consisting of a head element and
  ||| the rest of the list, of length `len`.
  (::) : (x : elem) -> (xs : Vect len elem) -> Vect (S len) elem

-- Hints for interactive editing
%name Vect xs,ys,zs,ws

export
length : (xs : Vect len elem) -> Nat
length [] = 0
length (x::xs) = 1 + length xs

||| Show that the length function on vectors in fact calculates the length
private 
lengthCorrect : (len : Nat) -> (xs : Vect len elem) -> length xs = len
lengthCorrect Z     []        = Refl
lengthCorrect (S n) (x :: xs) = rewrite lengthCorrect n xs in Refl

--------------------------------------------------------------------------------
-- Indexing into vectors
--------------------------------------------------------------------------------

||| All but the first element of the vector
|||
||| ```idris example
||| tail [1,2,3,4]
||| ```
public export
tail : Vect (S len) elem -> Vect len elem
tail (x::xs) = xs

||| Only the first element of the vector
|||
||| ```idris example
||| head [1,2,3,4]
||| ```
public export
head : Vect (S len) elem -> elem
head (x::xs) = x

||| The last element of the vector
|||
||| ```idris example
||| last [1,2,3,4]
||| ```
public export
last : Vect (S len) elem -> elem
last (x::[])    = x
last (x::y::ys) = last $ y::ys

||| All but the last element of the vector
|||
||| ```idris example
||| init [1,2,3,4]
||| ```
public export
init : Vect (S len) elem -> Vect len elem
init (x::[])    = []
init (x::y::ys) = x :: init (y::ys)

||| Extract a particular element from a vector
|||
||| ```idris example
||| index 1 [1,2,3,4]
||| ```
export
index : Fin len -> Vect len elem -> elem
index FZ     (x::xs) = x
index (FS k) (x::xs) = index k xs

||| Insert an element at a particular index
|||
||| ```idris example
||| insertAt 1 8 [1,2,3,4]
||| ```
export
insertAt : Fin (S len) -> elem -> Vect len elem -> Vect (S len) elem
insertAt FZ     y xs      = y :: xs
insertAt (FS k) y (x::xs) = x :: insertAt k y xs
insertAt (FS k) y []      = absurd k

||| Construct a new vector consisting of all but the indicated element
|||
||| ```idris example
||| deleteAt 1 [1,2,3,4]
||| ```
export
deleteAt : Fin (S len) -> Vect (S len) elem -> Vect len elem
deleteAt             FZ     (x::xs) = xs
deleteAt {len = S m} (FS k) (x::xs) = x :: deleteAt k xs
deleteAt {len = Z}   (FS k) (x::xs) impossible
deleteAt             _      []      impossible

||| Replace an element at a particlar index with another
|||
||| ```idris example
||| replaceAt 1 8 [1,2,3,4]
||| ```
export
replaceAt : Fin len -> elem -> Vect len elem -> Vect len elem
replaceAt FZ     y (x::xs) = y :: xs
replaceAt (FS k) y (x::xs) = x :: replaceAt k y xs

||| Replace the element at a particular index with the result of applying a function to it
||| @ i the index to replace at
||| @ f the update function
||| @ xs the vector to replace in
|||
||| ```idris example
||| updateAt 1 (+10) [1,2,3,4]
||| ```
export
updateAt : (i : Fin len) -> (f : elem -> elem) -> (xs : Vect len elem) -> Vect len elem
updateAt FZ     f (x::xs) = f x :: xs
updateAt (FS k) f (x::xs) = x :: updateAt k f xs


||| Append two vectors
|||
||| ```idris example
||| [1,2,3,4] ++ [5,6]
||| ```
public export
(++) : (xs : Vect m elem) -> (ys : Vect n elem) -> Vect (m + n) elem
(++) []      ys = ys
(++) (x::xs) ys = x :: xs ++ ys

||| Repeate some value some number of times.
|||
||| @ len the number of times to repeat it
||| @ x the value to repeat
|||
||| ```idris example
||| replicate 4 1
||| ```
public export
replicate : (len : Nat) -> (x : elem) -> Vect len elem
replicate Z     x = []
replicate (S k) x = x :: replicate k x

||| Merge two ordered vectors
|||
||| ```idris example
||| mergeBy compare (fromList [1,3,5]) (fromList [2,3,4,5,6])
||| ```
export
mergeBy : (elem -> elem -> Ordering) -> (xs : Vect n elem) -> (ys : Vect m elem) -> Vect (n + m) elem
mergeBy order [] [] = []
mergeBy order [] (x :: xs) = x :: xs
mergeBy {n = S k} order (x :: xs) [] = rewrite plusZeroRightNeutral (S k) in
                                               x :: xs
mergeBy {n = S k} {m = S k'} order (x :: xs) (y :: ys)
     = case order x y of
            LT => x :: mergeBy order xs (y :: ys)
            _  => rewrite sym (plusSuccRightSucc k k') in
                             y :: mergeBy order (x :: xs) ys

export
merge : Ord elem => Vect n elem -> Vect m elem -> Vect (n + m) elem
merge = mergeBy compare

--------------------------------------------------------------------------------
-- Transformations
--------------------------------------------------------------------------------

||| Reverse the order of the elements of a vector
|||
||| ```idris example
||| reverse [1,2,3,4]
||| ```
export
reverse : Vect len elem -> Vect len elem
reverse xs = go [] xs
  where go : Vect n elem -> Vect m elem -> Vect (n+m) elem
        go {n}         acc []        = rewrite plusZeroRightNeutral n in acc
        go {n} {m=S m} acc (x :: xs) = rewrite sym $ plusSuccRightSucc n m
                                       in go (x::acc) xs

||| Alternate an element between the other elements of a vector
||| @ sep the element to intersperse
||| @ xs the vector to separate with `sep`
|||
||| ```idris example
||| intersperse 0 [1,2,3,4]
||| ```
export
intersperse : (sep : elem) -> (xs : Vect len elem) -> Vect (len + pred len) elem
intersperse sep []      = []
intersperse sep (x::xs) = x :: intersperse' sep xs
  where
    intersperse' : elem -> Vect n elem -> Vect (n + n) elem
    intersperse'         sep []      = []
    intersperse' {n=S n} sep (x::xs) = rewrite sym $ plusSuccRightSucc n n
                                       in sep :: x :: intersperse' sep xs

--------------------------------------------------------------------------------
-- Conversion from list (toList is provided by Foldable)
--------------------------------------------------------------------------------

export
fromList' : Vect len elem -> (l : List elem) -> Vect (length l + len) elem
fromList' ys [] = ys
fromList' {len} ys (x::xs) =
  rewrite (plusSuccRightSucc (length xs) len) in
  fromList' (x::ys) xs

||| Convert a list to a vector.
|||
||| The length of the list should be statically known.
|||
||| ```idris example
||| fromList [1,2,3,4]
||| ```
export
fromList : (l : List elem) -> Vect (length l) elem
fromList l =
  rewrite (sym $ plusZeroRightNeutral (length l)) in
  reverse $ fromList' [] l

--------------------------------------------------------------------------------
-- Zips and unzips
--------------------------------------------------------------------------------

||| Combine two equal-length vectors pairwise with some function.
|||
||| @ f the function to combine elements with
||| @ xs the first vector of elements
||| @ ys the second vector of elements
|||
||| ```idris example
||| zipWith (+) (fromList [1,2,3,4]) (fromList [5,6,7,8])
||| ```
public export
zipWith : (f : a -> b -> c) -> (xs : Vect n a) -> (ys : Vect n b) -> Vect n c
zipWith f []      []      = []
zipWith f (x::xs) (y::ys) = f x y :: zipWith f xs ys

||| Combine three equal-length vectors into a vector with some function
|||
||| ```idris example
||| zipWith3 (\x,y,z => x+y+z) (fromList [1,2,3,4]) (fromList [5,6,7,8]) (fromList [1,1,1,1])
||| ```
public export
zipWith3 : (a -> b -> c -> d) -> (xs : Vect n a) -> (ys : Vect n b) -> (zs : Vect n c) -> Vect n d
zipWith3 f []      []      []      = []
zipWith3 f (x::xs) (y::ys) (z::zs) = f x y z :: zipWith3 f xs ys zs

||| Combine two equal-length vectors pairwise
|||
||| ```idris example
||| zip (fromList [1,2,3,4]) (fromList [1,2,3,4])
||| ```
public export
zip : (xs : Vect n a) -> (ys : Vect n b) -> Vect n (a, b)
zip = zipWith (\x,y => (x,y))

||| Combine three equal-length vectors elementwise into a vector of tuples
|||
||| ```idris example
||| zip3 (fromList [1,2,3,4]) (fromList [1,2,3,4]) (fromList [1,2,3,4])
||| ```
public export
zip3 : (xs : Vect n a) -> (ys : Vect n b) -> (zs : Vect n c) -> Vect n (a, b, c)
zip3 = zipWith3 (\x,y,z => (x,y,z))

||| Convert a vector of pairs to a pair of vectors
|||
||| ```idris example
||| unzip (fromList [(1,2), (1,2)])
||| ```
export
unzip : (xs : Vect n (a, b)) -> (Vect n a, Vect n b)
unzip []           = ([], [])
unzip ((l, r)::xs) with (unzip xs)
  unzip ((l, r)::xs) | (lefts, rights) = (l::lefts, r::rights)

||| Convert a vector of three-tuples to a triplet of vectors
|||
||| ```idris example
||| unzip3 (fromList [(1,2,3), (1,2,3)])
||| ```
export
unzip3 : (xs : Vect n (a, b, c)) -> (Vect n a, Vect n b, Vect n c)
unzip3 []            = ([], [], [])
unzip3 ((l,c,r)::xs) with (unzip3 xs)
  unzip3 ((l,c,r)::xs) | (lefts, centers, rights) 
      = (l::lefts, c::centers, r::rights)

--------------------------------------------------------------------------------
-- Equality
--------------------------------------------------------------------------------

export
implementation (Eq elem) => Eq (Vect len elem) where
  (==) []      []      = True
  (==) (x::xs) (y::ys) = x == y && xs == ys


--------------------------------------------------------------------------------
-- Order
--------------------------------------------------------------------------------

export
implementation Ord elem => Ord (Vect len elem) where
  compare []      []      = EQ
  compare (x::xs) (y::ys) 
      = case compare x y of
             EQ => compare xs ys
             x => x

--------------------------------------------------------------------------------
-- Maps
--------------------------------------------------------------------------------

export
implementation Functor (Vect n) where
  map f []        = []
  map f (x::xs) = f x :: map f xs

||| Map a partial function across a vector, returning those elements for which
||| the function had a value.
|||
||| The first projection of the resulting pair (ie the length) will always be
||| at most the length of the input vector. This is not, however, guaranteed
||| by the type.
|||
||| @ f the partial function (expressed by returning `Maybe`)
||| @ xs the vector to check for results
|||
||| ```idris example
||| mapMaybe ((find (=='a')) . unpack) (fromList ["abc","ade","bgh","xyz"])
||| ```
export
mapMaybe : (f : a -> Maybe b) -> (xs : Vect len a) -> (m : Nat ** Vect m b)
mapMaybe f []      = (_ ** [])
mapMaybe f (x::xs) =
  let (len ** ys) = mapMaybe f xs
  in case f x of
       Just y  => (S len ** y :: ys)
       Nothing => (  len **      ys)

--------------------------------------------------------------------------------
-- Folds
--------------------------------------------------------------------------------

public export
foldrImpl : (t -> acc -> acc) -> acc -> (acc -> acc) -> Vect n t -> acc
foldrImpl f e go [] = go e
foldrImpl f e go (x::xs) = foldrImpl f e (go . (f x)) xs

export
implementation Foldable (Vect n) where
  foldr f e xs = foldrImpl f e id xs

--------------------------------------------------------------------------------
-- Special folds
--------------------------------------------------------------------------------

||| Flatten a vector of equal-length vectors
|||
||| ```idris example
||| concat [[1,2,3], [4,5,6]]
||| ```
public export
concat : (xss : Vect m (Vect n elem)) -> Vect (m * n) elem
concat []      = []
concat (v::vs) = v ++ Vect.concat vs

||| Foldr without seeding the accumulator
|||
||| ```idris example
||| foldr1 (-) (fromList [1,2,3])
||| ```
public export
foldr1 : (t -> t -> t) -> Vect (S n) t -> t
foldr1 f [x]        = x
foldr1 f (x::y::xs) = f x (foldr1 f (y::xs))

||| Foldl without seeding the accumulator
|||
||| ```idris example
||| foldl1 (-) (fromList [1,2,3])
||| ```
public export
foldl1 : (t -> t -> t) -> Vect (S n) t -> t
foldl1 f (x::xs) = foldl f x xs
--------------------------------------------------------------------------------
-- Scans
--------------------------------------------------------------------------------

||| The scanl function is similar to foldl, but returns all the intermediate
||| accumulator states in the form of a vector.
|||
||| ```idris example
||| scanl (-) 0 (fromList [1,2,3])
||| ```
public export
scanl : (res -> elem -> res) -> res -> Vect len elem -> Vect (S len) res
scanl f q []      = [q]
scanl f q (x::xs) = q :: scanl f (f q x) xs

||| The scanl1 function is a variant of scanl that doesn't require an explicit
||| starting value.
||| It assumes the first element of the vector to be the starting value and then
||| starts the fold with the element following it.
|||
||| ```idris example
||| scanl1 (-) (fromList [1,2,3])
||| ```
public export
scanl1 : (elem -> elem -> elem) -> Vect len elem -> Vect len elem
scanl1 f [] = []
scanl1 f (x::xs) = scanl f x xs

--------------------------------------------------------------------------------
-- Membership tests
--------------------------------------------------------------------------------

||| Search for an item using a user-provided test
||| @ p the equality test
||| @ e the item to search for
||| @ xs the vector to search in
|||
||| ```idris example
||| elemBy (==) 2 [1,2,3,4]
||| ```
public export
elemBy : (p : elem -> elem -> Bool) -> (e : elem) -> (xs : Vect len elem) -> Bool
elemBy p e []      = False
elemBy p e (x::xs) = p e x || elemBy p e xs

||| Use the default Boolean equality on elements to search for an item
||| @ x what to search for
||| @ xs where to search
|||
||| ```idris example
||| elem 3 [1,2,3,4]
||| ```
public export
elem : Eq elem => (x : elem) -> (xs : Vect len elem) -> Bool
elem = elemBy (==)

||| Find the association of some key with a user-provided comparison
||| @ p the comparison operator for keys (True if they match)
||| @ e the key to look for
|||
||| ```idris example
||| lookupBy (==) 2 [(1, 'a'), (2, 'b'), (3, 'c')]
||| ```
public export
lookupBy : (p : key -> key -> Bool) -> (e : key) -> (xs : Vect n (key, val)) -> Maybe val
lookupBy p e []           = Nothing
lookupBy p e ((l, r)::xs) = if p e l then Just r else lookupBy p e xs

||| Find the assocation of some key using the default Boolean equality test
|||
||| ```idris example
||| lookup 3 [(1, 'a'), (2, 'b'), (3, 'c')]
||| ```
public export
lookup : Eq key => key -> Vect n (key, val) -> Maybe val
lookup = lookupBy (==)

||| Check if any element of xs is found in elems by a user-provided comparison
||| @ p the comparison operator
||| @ elems the vector to search
||| @ xs what to search for
|||
||| ```idris example
||| hasAnyBy (==) [2,5] [1,2,3,4]
||| ```
public export
hasAnyBy : (p : elem -> elem -> Bool) -> (elems : Vect m elem) -> (xs : Vect len elem) -> Bool
hasAnyBy p elems []      = False
hasAnyBy p elems (x::xs) = elemBy p x elems || hasAnyBy p elems xs

||| Check if any element of xs is found in elems using the default Boolean equality test
|||
||| ```idris example
||| hasAny [2,5] [1,2,3,4]
||| ```
public export
hasAny : Eq elem => Vect m elem -> Vect len elem -> Bool
hasAny = hasAnyBy (==)

--------------------------------------------------------------------------------
-- Searching with a predicate
--------------------------------------------------------------------------------

||| Find the first element of the vector that satisfies some test
||| @ p the test to satisfy
|||
||| ```idris example
||| find (== 3) [1,2,3,4]
||| ```
public export
find : (p : elem -> Bool) -> (xs : Vect len elem) -> Maybe elem
find p []      = Nothing
find p (x::xs) = if p x then Just x else find p xs

||| Find the index of the first element of the vector that satisfies some test
|||
||| ```idris example
||| findIndex (== 3) [1,2,3,4]
||| ```
public export
findIndex : (elem -> Bool) -> Vect len elem -> Maybe (Fin len)
findIndex p []        = Nothing
findIndex p (x :: xs) = if p x then Just FZ else map FS (findIndex p xs)

||| Find the indices of all elements that satisfy some test
|||
||| ```idris example
||| findIndices (< 3) [1,2,3,4]
||| ```
public export
findIndices : (elem -> Bool) -> Vect m elem -> List (Fin m)
findIndices p []        = []
findIndices p (x :: xs) 
     = let is = map FS $ findIndices p xs in
           if p x then FZ :: is else is

||| Find the index of the first element of the vector that satisfies some test
|||
||| ```idris example
||| elemIndexBy (==) 3 [1,2,3,4]
||| ```
public export
elemIndexBy : (elem -> elem -> Bool) -> elem -> Vect m elem -> Maybe (Fin m)
elemIndexBy p e = findIndex $ p e

||| Find the index of the first element of the vector equal to the given one.
|||
||| ```idris example
||| elemIndex 3 [1,2,3,4]
||| ```
public export
elemIndex : Eq elem => elem -> Vect m elem -> Maybe (Fin m)
elemIndex = elemIndexBy (==)

||| Find the indices of all elements that satisfy some test
|||
||| ```idris example
||| elemIndicesBy (<=) 3 [1,2,3,4]
||| ```
public export
elemIndicesBy : (elem -> elem -> Bool) -> elem -> Vect m elem -> List (Fin m)
elemIndicesBy p e = findIndices $ p e

||| Find the indices of all elements uquals to the given one
|||
||| ```idris example
||| elemIndices 3 [1,2,3,4,3]
||| ```
public export
elemIndices : Eq elem => elem -> Vect m elem -> List (Fin m)
elemIndices = elemIndicesBy (==)



