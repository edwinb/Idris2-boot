module Prelude

import public Builtin
import public PrimIO

{-
The Prelude is minimal (since it is effectively part of the language
specification, this seems to be desirable - we should, nevertheless, aim to
provide a good selection of base libraries). A rule of thumb is that it should
contain the basic functions required by almost any non-trivial program.

As such, it should contain:

- Anything the elaborator can desugar to (e.g. pairs, unit, =, laziness)
- Basic types Bool, Nat, List, Dec, Maybe, Either
- The most important utility functions: id, the, composition, etc
- Interfaces for arithmetic and implementations for the primitives and
  basic types
- Char and String manipulation
- Show, Eq, Ord, and implementations for all types in the prelude
- Interfaces and functions for basic proof (cong, Uninhabited, etc) --
- Semigroup, Monoid
- Functor, Applicative, Monad and related functions
- Foldable
- [TODO: Enum for range syntax]
- Console IO

Everything else should be in the base libraries, and imported as required.
In particular, proofs of Nat/List properties that almost never get used in
practice would probably be better in base libraries.

(These guidelines will probably get revised a few times.)
-}

-- Numerical operators
infix 6 ==, /=, <, <=, >, >=
infixl 7 <<, >> -- unused
infixl 8 +, -
infixl 9 *, /

-- Boolean operators
infixr 4 &&
infixr 5 ||

-- List and String operators
infixr 7 ::, ++

-- Functor/Applicative/Monad/Algebra operators
infixl 1 >>=
infixr 2 <|>
infixl 3 <*>, *>, <*
infixr 4 <$>
infixl 6 <+>

-- Utility operators
infixr 9 .
infixr 0 $

infixl 9 `div`, `mod`

-----------------------
-- UTILITY FUNCTIONS --
-----------------------

public export %inline
the : (0 a : Type) -> (1 x : a) -> a
the _ x = x

public export %inline
id : (1 x : a) -> a           -- Hopefully linearity annotation won't
                              -- break equality proofs involving id
id x = x

public export %inline
const : a -> b -> a
const x = \value => x

public export %inline
(.) : (b -> c) -> (a -> b) -> a -> c
(.) f g = \x => f (g x)

public export
flip : (f : a -> b -> c) -> b -> a -> c
flip f x y = f y x

public export
apply : (a -> b) -> a -> b
apply f a = f a

public export
curry : ((a, b) -> c) -> a -> b -> c
curry f a b = f (a, b)

public export
uncurry : (a -> b -> c) -> (a, b) -> c
uncurry f (a, b) = f a b

-- $ is compiled specially to shortcut any tricky unification issues, but if
-- it did have a type this is what it would be, and it might be useful to
-- use directly sometimes (e.g. in higher order functions)
public export
($) : forall a, b . ((x : a) -> b x) -> (x : a) -> b x
($) f a = f a

-------------------
-- PROOF HELPERS --
-------------------

public export
cong : (f : t -> u) -> (1 p : a = b) -> f a = f b
cong f Refl = Refl

public export
interface Uninhabited t where
  uninhabited : t -> Void

%extern
public export
void : Void -> a

export
Uninhabited Void where
  uninhabited = id

public export
absurd : Uninhabited t => (h : t) -> a
absurd h = void (uninhabited h)

public export
Not : Type -> Type
Not x = x -> Void

--------------
-- BOOLEANS --
--------------

public export
data Bool = True | False

public export
not : (1 b : Bool) -> Bool
not True = False
not False = True

public export
(&&) : (1 b : Bool) -> Lazy Bool -> Bool
(&&) True x = x
(&&) False x = False

public export
(||) : (1 b : Bool) -> Lazy Bool -> Bool
(||) True x = True
(||) False x = x

%inline
public export
intToBool : Int -> Bool
intToBool 0 = False
intToBool x = True

------------------------
-- EQUALITY, ORDERING --
------------------------

public export
interface Eq ty where
  (==) : ty -> ty -> Bool
  (/=) : ty -> ty -> Bool

  x == y = not (x /= y)
  x /= y = not (x == y)

public export
Eq () where
  _ == _ = True

public export
Eq Bool where
  True == True = True
  False == False = True
  _ == _ = False

public export
Eq Int where
  x == y = intToBool (prim__eq_Int x y)

public export
Eq Integer where
  x == y = intToBool (prim__eq_Integer x y)

public export
Eq Double where
  x == y = intToBool (prim__eq_Double x y)

public export
Eq Char where
  x == y = intToBool (prim__eq_Char x y)

public export
Eq String where
  x == y = intToBool (prim__eq_String x y)

public export
Eq a => Eq b => Eq (a, b) where
  (x1, y1) == (x2, y2) = x1 == x2 && y1 == y2

public export
data Ordering = LT | EQ | GT

public export
Eq Ordering where
  LT == LT = True
  EQ == EQ = True
  GT == GT = True
  _  == _  = False

public export
interface Eq ty => Ord ty where
  compare : ty -> ty -> Ordering

  (<) : ty -> ty -> Bool
  (<) x y = compare x y == LT

  (>) : ty -> ty -> Bool
  (>) x y = compare x y == GT

  (<=) : ty -> ty -> Bool
  (<=) x y = compare x y /= GT

  (>=) : ty -> ty -> Bool
  (>=) x y = compare x y /= LT

  max : ty -> ty -> ty
  max x y = if x > y then x else y

  min : ty -> ty -> ty
  min x y = if (x < y) then x else y

public export
Ord () where
  compare _ _ = EQ

public export
Ord Bool where
  compare False False = EQ
  compare False True = LT
  compare True False = GT
  compare True True = EQ

public export
Ord Int where
  compare x y = if x < y then LT else if x == y then EQ else GT

  (<) x y = intToBool (prim__lt_Int x y)
  (<=) x y = intToBool (prim__lte_Int x y)
  (>) x y = intToBool (prim__gt_Int x y)
  (>=) x y = intToBool (prim__gte_Int x y)

public export
Ord Integer where
  compare x y = if x < y then LT else if x == y then EQ else GT

  (<) x y = intToBool (prim__lt_Integer x y)
  (<=) x y = intToBool (prim__lte_Integer x y)
  (>) x y = intToBool (prim__gt_Integer x y)
  (>=) x y = intToBool (prim__gte_Integer x y)

public export
Ord Double where
  compare x y = if x < y then LT else if x == y then EQ else GT

  (<) x y = intToBool (prim__lt_Double x y)
  (<=) x y = intToBool (prim__lte_Double x y)
  (>) x y = intToBool (prim__gt_Double x y)
  (>=) x y = intToBool (prim__gte_Double x y)

public export
Ord String where
  compare x y = if x < y then LT else if x == y then EQ else GT

  (<) x y = intToBool (prim__lt_String x y)
  (<=) x y = intToBool (prim__lte_String x y)
  (>) x y = intToBool (prim__gt_String x y)
  (>=) x y = intToBool (prim__gte_String x y)

public export
Ord Char where
  compare x y = if x < y then LT else if x == y then EQ else GT

  (<) x y = intToBool (prim__lt_Char x y)
  (<=) x y = intToBool (prim__lte_Char x y)
  (>) x y = intToBool (prim__gt_Char x y)
  (>=) x y = intToBool (prim__gte_Char x y)

public export
Ord a => Ord b => Ord (a, b) where
  compare (x1, y1) (x2, y2)
      = if x1 /= x2 then compare x1 x2
                    else compare y1 y2

------------------------
-- NUMERIC INTERFACES --
------------------------

%integerLit fromInteger

public export
interface Num ty where
  (+) : ty -> ty -> ty
  (*) : ty -> ty -> ty
  fromInteger : Integer -> ty

%allow_overloads fromInteger

public export
interface Num ty => Neg ty where
  negate : ty -> ty
  (-) : ty -> ty -> ty

public export
interface Num ty => Abs ty where
  abs : ty -> ty

public export
interface Num ty => Fractional ty where
  (/) : ty -> ty -> ty
  recip : ty -> ty

  recip x = 1 / x

public export
interface Num ty => Integral ty where
  div : ty -> ty -> ty
  mod : ty -> ty -> ty

----- instances for primitives
-- Integer

public export
Num Integer where
  (+) = prim__add_Integer
  (*) = prim__mul_Integer
  fromInteger = id

public export
Neg Integer where
  negate x = prim__sub_Integer 0 x
  (-) = prim__sub_Integer

public export
Abs Integer where
  abs x = if x < 0 then -x else x

public export
Integral Integer where
  div x y
      = case y == 0 of
             False => prim__div_Integer x y
  mod x y
      = case y == 0 of
             False => prim__mod_Integer x y

-- This allows us to pick integer as a default at the end of elaboration if
-- all other possibilities fail. I don't plan to provide a nicer syntax for
-- this...
%defaulthint
public export
defaultInteger : Num Integer
defaultInteger = %search

-- Int

public export
Num Int where
  (+) = prim__add_Int
  (*) = prim__mul_Int
  fromInteger = prim__cast_IntegerInt

public export
Neg Int where
  negate x = prim__sub_Int 0 x
  (-) = prim__sub_Int

public export
Abs Int where
  abs x = if x < 0 then -x else x

public export
Integral Int where
  div x y
      = case y == 0 of
             False => prim__div_Int x y
  mod x y
      = case y == 0 of
             False => prim__mod_Int x y

-- Double

public export
Num Double where
  (+) = prim__add_Double
  (*) = prim__mul_Double
  fromInteger = prim__cast_IntegerDouble

public export
Neg Double where
  negate x = prim__negate_Double x
  (-) = prim__sub_Double

public export
Abs Double where
  abs x = if x < 0 then -x else x

public export
Fractional Double where
  (/) = prim__div_Double

-------------
-- ALGEBRA --
-------------

public export
interface Semigroup ty where
  (<+>) : ty -> ty -> ty

public export
interface Semigroup ty => Monoid ty where
  neutral : ty

export
shiftL : Int -> Int -> Int
shiftL = prim__shl_Int

export
shiftR : Int -> Int -> Int
shiftR = prim__shr_Int

---------------------------------
-- FUNCTOR, APPLICATIVE, ALTERNATIVE, MONAD --
---------------------------------

public export
interface Functor f where
  map : (a -> b) -> f a -> f b

public export
(<$>) : Functor f => (func : a -> b) -> f a -> f b
(<$>) func x = map func x

public export
ignore : Functor f => f a -> f ()
ignore = map (const ())

public export
interface Functor f => Applicative f where
  pure : a -> f a
  (<*>) : f (a -> b) -> f a -> f b

public export
(<*) : Applicative f => f a -> f b -> f a
a <* b = map const a <*> b

public export
(*>) : Applicative f => f a -> f b -> f b
a *> b = map (const id) a <*> b

%allow_overloads pure
%allow_overloads (<*)
%allow_overloads (*>)

public export
interface Applicative f => Alternative f where
  empty : f a
  (<|>) : f a -> f a -> f a

public export
interface Applicative m => Monad m where
  (>>=) : m a -> (a -> m b) -> m b
  join : m (m a) -> m a

  -- default implementations
  (>>=) x f = join (f <$> x)
  join x = x >>= id

%allow_overloads (>>=)

public export
guard : Alternative f => Bool -> f ()
guard x = if x then pure () else empty

public export
when : Applicative f => Bool -> Lazy (f ()) -> f ()
when True f = f
when False f = pure ()

---------------------------
-- FOLDABLE, TRAVERSABLE --
---------------------------

public export
interface Foldable (t : Type -> Type) where
  foldr : (func : elem -> acc -> acc) -> (init : acc) -> (input : t elem) -> acc
  foldl : (func : acc -> elem -> acc) -> (init : acc) -> (input : t elem) -> acc
  foldl f z t = foldr (flip (.) . flip f) id t z

public export
concat : (Foldable t, Monoid a) => t a -> a
concat = foldr (<+>) neutral

public export
concatMap : (Foldable t, Monoid m) => (a -> m) -> t a -> m
concatMap f = foldr ((<+>) . f) neutral

public export
and : Foldable t => t (Lazy Bool) -> Bool
and = foldl (&&) True

public export
or : Foldable t => t (Lazy Bool) -> Bool
or = foldl (||) False

public export
any : Foldable t => (a -> Bool) -> t a -> Bool
any p = foldl (\x,y => x || p y) False

public export
all : Foldable t => (a -> Bool) -> t a -> Bool
all p = foldl (\x,y => x && p y)  True

public export
sum : (Foldable t, Num a) => t a -> a
sum = foldr (+) 0

public export
product : (Foldable t, Num a) => t a -> a
product = foldr (*) 1

public export
traverse_ : (Foldable t, Applicative f) => (a -> f b) -> t a -> f ()
traverse_ f = foldr ((*>) . f) (pure ())

||| Evaluate each computation in a structure and discard the results
public export
sequence_ : (Foldable t, Applicative f) => t (f a) -> f ()
sequence_ = foldr (*>) (pure ())

||| Like `traverse_` but with the arguments flipped
public export
for_ : (Foldable t, Applicative f) => t a -> (a -> f b) -> f ()
for_ = flip traverse_

||| Fold using Alternative
|||
||| If you have a left-biased alternative operator `<|>`, then `choice`
||| performs left-biased choice from a list of alternatives, which means that
||| it evaluates to the left-most non-`empty` alternative.
|||
||| If the list is empty, or all values in it are `empty`, then it
||| evaluates to `empty`.
|||
||| Example:
|||
||| ```
||| -- given a parser expression like:
||| expr = literal <|> keyword <|> funcall
|||
||| -- choice lets you write this as:
||| expr = choice [literal, keyword, funcall]
||| ```
|||
||| Note: In Haskell, `choice` is called `asum`.
public export
choice : (Foldable t, Alternative f) => t (f a) -> f a
choice = foldr (<|>) empty

||| A fused version of `choice` and `map`.
public export
choiceMap : (Foldable t, Alternative f) => (a -> f b) -> t a -> f b
choiceMap f = foldr (\e, a => f e <|> a) empty

public export
interface (Functor t, Foldable t) => Traversable (t : Type -> Type) where
  ||| Map each element of a structure to a computation, evaluate those
  ||| computations and combine the results.
  traverse : Applicative f => (a -> f b) -> t a -> f (t b)

||| Evaluate each computation in a structure and collect the results
public export
sequence : (Traversable t, Applicative f) => t (f a) -> f (t a)
sequence = traverse id

||| Like `traverse` but with the arguments flipped
public export
for : (Traversable t, Applicative f) => t a -> (a -> f b) -> f (t b)
for = flip traverse

-----------
-- NATS ---
-----------

public export
data Nat = Z | S Nat

%name Nat k, j, i

public export
integerToNat : Integer -> Nat
integerToNat x
  = if intToBool (prim__lte_Integer x 0)
       then Z
       else S (assert_total (integerToNat (prim__sub_Integer x 1)))

-- Define separately so we can spot the name when optimising Nats
public export
plus : (1 x : Nat) -> (1 y : Nat) -> Nat
plus Z y = y
plus (S k) y = S (plus k y)

public export
minus : (1 left : Nat) -> Nat -> Nat
minus Z        right     = Z
minus left     Z         = left
minus (S left) (S right) = minus left right

public export
mult : (1 x : Nat) -> Nat -> Nat
mult Z y = Z
mult (S k) y = plus y (mult k y)

public export
Num Nat where
  (+) = plus
  (*) = mult

  fromInteger x = integerToNat x

public export
Eq Nat where
  Z == Z = True
  S j == S k = j == k
  _ == _ = False

public export
Ord Nat where
  compare Z Z = EQ
  compare Z (S k) = LT
  compare (S k) Z = GT
  compare (S j) (S k) = compare j k

public export
natToInteger : Nat -> Integer
natToInteger Z = 0
natToInteger (S k) = 1 + natToInteger k 
                         -- integer (+) may be non-linear in second
                         -- argument


-----------
-- PAIRS --
-----------

public export
Functor (Pair a) where
  map f (x, y) = (x, f y)

public export
mapFst : (a -> c) -> (a, b) -> (c, b)
mapFst f (x, y) = (f x, y)

-----------
-- MAYBE --
-----------

public export
data Maybe : (ty : Type) -> Type where
  Nothing : Maybe ty
  Just : (1 x : ty) -> Maybe ty

public export
maybe : Lazy b -> Lazy (a -> b) -> Maybe a -> b
maybe n j Nothing  = n
maybe n j (Just x) = j x

public export
Eq a => Eq (Maybe a) where
  Nothing  == Nothing  = True
  Nothing  == (Just _) = False
  (Just _) == Nothing  = False
  (Just a) == (Just b) = a == b

public export
Ord a => Ord (Maybe a) where
  compare Nothing  Nothing  = EQ
  compare Nothing  (Just _) = LT
  compare (Just _) Nothing  = GT
  compare (Just a) (Just b) = compare a b

public export
Semigroup (Maybe a) where
  Nothing   <+> m = m
  (Just x)  <+> _ = Just x

public export
Monoid (Maybe a) where
  neutral = Nothing

public export
Functor Maybe where
  map f (Just x) = Just (f x)
  map f Nothing  = Nothing

public export
Applicative Maybe where
  pure = Just

  Just f <*> Just a = Just (f a)
  _      <*> _        = Nothing

public export
Alternative Maybe where
    empty = Nothing

    (Just x) <|> _ = Just x
    Nothing  <|> v = v

public export
Monad Maybe where
  Nothing  >>= k = Nothing
  (Just x) >>= k = k x

public export
Foldable Maybe where
  foldr _ z Nothing  = z
  foldr f z (Just x) = f x z

public export
Traversable Maybe where
  traverse f Nothing = pure Nothing
  traverse f (Just x) = (pure Just) <*> (f x)

---------
-- DEC --
---------

public export
data Dec : Type -> Type where
  Yes : (prf : prop) -> Dec prop
  No  : (contra : prop -> Void) -> Dec prop

------------
-- EITHER --
------------

public export
data Either : (a : Type) -> (b : Type) -> Type where
     Left : forall a, b. (1 x : a) -> Either a b
     Right : forall a, b. (1 x : b) -> Either a b

public export
either : Lazy (a -> c) -> Lazy (b -> c) -> Either a b -> c
either l r (Left x) = l x
either l r (Right x) = r x

public export
(Eq a, Eq b) => Eq (Either a b) where
  Left x == Left x' = x == x'
  Right x == Right x' = x == x'
  _ == _ = False

public export
Functor (Either e) where
  map f (Left x) = Left x
  map f (Right x) = Right (f x)

public export
Applicative (Either e) where
    pure = Right

    (Left a) <*> _          = Left a
    (Right f) <*> (Right r) = Right (f r)
    (Right _) <*> (Left l)  = Left l

public export
Monad (Either e) where
    (Left n) >>= _ = Left n
    (Right r) >>= f = f r

-----------
-- LISTS --
-----------

public export
data List a = Nil | (::) a (List a)

%name List xs, ys, zs

public export
Eq a => Eq (List a) where
  [] == [] = True
  x :: xs == y :: ys = x == y && xs == ys
  _ == _ = False

public export
Ord a => Ord (List a) where
  compare [] [] = EQ
  compare [] (x :: xs) = LT
  compare (x :: xs) [] = GT
  compare (x :: xs) (y ::ys)
     = case compare x y of
            EQ => compare xs ys
            c => c

namespace List
  public export
  (++) : (1 xs : List a) -> List a -> List a
  [] ++ ys = ys
  (x :: xs) ++ ys = x :: xs ++ ys

public export
Functor List where
  map f [] = []
  map f (x :: xs) = f x :: map f xs

public export
Semigroup (List a) where
  (<+>) = (++)

public export
Monoid (List a) where
  neutral = []

public export
Foldable List where
  foldr c n [] = n
  foldr c n (x::xs) = c x (foldr c n xs)

  foldl f q [] = q
  foldl f q (x::xs) = foldl f (f q x) xs

public export
Applicative List where
  pure x = [x]
  fs <*> vs = concatMap (\f => map f vs) fs

public export
Alternative List where
    empty = []
    (<|>) = (++)

public export
Monad List where
  m >>= f = concatMap f m

public export
Traversable List where
  traverse f [] = pure []
  traverse f (x::xs) = pure (::) <*> (f x) <*> (traverse f xs)

public export
elem : Eq a => a -> List a -> Bool
x `elem` [] = False
x `elem` (y :: ys) = if x == y then True else x `elem` ys

-------------
-- STREAMS --
-------------

namespace Stream
  public export
  data Stream : Type -> Type where
       (::) : a -> Inf (Stream a) -> Stream a

public export
Functor Stream where
  map f (x :: xs) = f x :: map f xs

public export
head : Stream a -> a
head (x :: xs) = x

public export
tail : Stream a -> Stream a
tail (x :: xs) = xs

public export
take : (1 n : Nat) -> Stream a -> List a
take Z xs = []
take (S k) (x :: xs) = x :: take k xs

-------------
-- STRINGS --
-------------

namespace Strings
  public export
  (++) : (1 x : String) -> (1 y : String) -> String
  x ++ y = prim__strAppend x y

public export
length : String -> Nat
length str = fromInteger (prim__cast_IntInteger (prim__strLength str))

public export
reverse : String -> String
reverse = prim__strReverse

public export
substr : Nat -> Nat -> String -> String
substr s e = prim__strSubstr (prim__cast_IntegerInt (natToInteger s))
                             (prim__cast_IntegerInt (natToInteger e))

public export
strCons : Char -> String -> String
strCons = prim__strCons

public export
strUncons : String -> Maybe (Char, String)
strUncons "" = Nothing
strUncons str = Just (prim__strHead str, prim__strTail str)

public export
pack : List Char -> String
pack [] = ""
pack (x :: xs) = strCons x (pack xs)

export
fastPack : List Char -> String
fastPack xs
   = unsafePerformIO (schemeCall String "string" (toFArgs xs))
  where
    toFArgs : List Char -> FArgList
    toFArgs [] = []
    toFArgs (x :: xs) = x :: toFArgs xs

public export
unpack : String -> List Char
unpack str = unpack' 0 (prim__cast_IntegerInt (natToInteger (length str))) str
  where
    unpack' : Int -> Int -> String -> List Char
    unpack' pos len str
        = if pos >= len
             then []
             else (prim__strIndex str pos) :: unpack' (pos + 1) len str


public export
Semigroup String where
  (<+>) = (++)

public export
Monoid String where
  neutral = ""

----------------
-- CHARACTERS --
----------------
public export
isUpper : Char -> Bool
isUpper x = x >= 'A' && x <= 'Z'

public export
isLower : Char -> Bool
isLower x = x >= 'a' && x <= 'z'

public export
isAlpha : Char -> Bool
isAlpha x = isUpper x || isLower x

public export
isDigit : Char -> Bool
isDigit x = (x >= '0' && x <= '9')

public export
isAlphaNum : Char -> Bool
isAlphaNum x = isDigit x || isAlpha x

public export
isSpace : Char -> Bool
isSpace x
    = x == ' '  || x == '\t' || x == '\r' ||
      x == '\n' || x == '\f' || x == '\v' ||
      x == '\xa0'

public export
isNL : Char -> Bool
isNL x = x == '\r' || x == '\n'

public export
toUpper : Char -> Char
toUpper x
    = if (isLower x)
         then prim__cast_IntChar (prim__cast_CharInt x - 32)
         else x

public export
toLower : Char -> Char
toLower x
    = if (isUpper x)
         then prim__cast_IntChar (prim__cast_CharInt x + 32)
         else x

public export
isHexDigit : Char -> Bool
isHexDigit x = elem (toUpper x) hexChars where
  hexChars : List Char
  hexChars
      = ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9',
         'A', 'B', 'C', 'D', 'E', 'F']

public export
isOctDigit : Char -> Bool
isOctDigit x = (x >= '0' && x <= '7')

public export
isControl : Char -> Bool
isControl x
    = (x >= '\x0000' && x <= '\x001f')
       || (x >= '\x007f' && x <= '\x009f')

----------
-- SHOW --
----------

public export
data Prec = Open | Equal | Dollar | Backtick | User Nat | PrefixMinus | App

public export
precCon : Prec -> Integer
precCon Open        = 0
precCon Equal       = 1
precCon Dollar      = 2
precCon Backtick    = 3
precCon (User n)    = 4
precCon PrefixMinus = 5
precCon App         = 6

export
Eq Prec where
  (==) (User m) (User n) = m == n
  (==) x        y        = precCon x == precCon y

export
Ord Prec where
  compare (User m) (User n) = compare m n
  compare x        y        = compare (precCon x) (precCon y)

public export
interface Show ty where
  show : (x : ty) -> String
  show x = showPrec Open x

  showPrec : (d : Prec) -> (x : ty) -> String
  showPrec _ x = show x

showParens : (1 b : Bool) -> String -> String
showParens False s = s
showParens True  s = "(" ++ s ++ ")"

export
showCon : (d : Prec) -> (conName : String) -> (shownArgs : String) -> String
showCon d conName shownArgs = showParens (d >= App) (conName ++ shownArgs)

export
showArg : Show a => (x : a) -> String
showArg x = " " ++ showPrec App x

firstCharIs : (Char -> Bool) -> String -> Bool
firstCharIs p "" = False
firstCharIs p str = p (assert_total (prim__strHead str))

primNumShow : (a -> String) -> Prec -> a -> String
primNumShow f d x = let str = f x in showParens (d >= PrefixMinus && firstCharIs (== '-') str) str

export
Show Int where
  showPrec = primNumShow prim__cast_IntString

export
Show Integer where
  showPrec = primNumShow prim__cast_IntegerString

export
Show Double where
  showPrec = primNumShow prim__cast_DoubleString

protectEsc : (Char -> Bool) -> String -> String -> String
protectEsc p f s = f ++ (if firstCharIs p s then "\\&" else "") ++ s

showLitChar : Char -> String -> String
showLitChar '\a'   = ("\\a" ++)
showLitChar '\b'   = ("\\b" ++)
showLitChar '\f'   = ("\\f" ++)
showLitChar '\n'   = ("\\n" ++)
showLitChar '\r'   = ("\\r" ++)
showLitChar '\t'   = ("\\t" ++)
showLitChar '\v'   = ("\\v" ++)
showLitChar '\SO'  = protectEsc (== 'H') "\\SO"
showLitChar '\DEL' = ("\\DEL" ++)
showLitChar '\\'   = ("\\\\" ++)
showLitChar c
    = case getAt (fromInteger (prim__cast_CharInteger c)) asciiTab of
           Just k => strCons '\\' . (k ++)
           Nothing => if (c > '\DEL')
                         then strCons '\\' . protectEsc isDigit (show (prim__cast_CharInt c))
                         else strCons c
  where
    asciiTab : List String
    asciiTab
        = ["NUL", "SOH", "STX", "ETX", "EOT", "ENQ", "ACK", "BEL",
           "BS",  "HT",  "LF",  "VT",  "FF",  "CR",  "SO",  "SI",
           "DLE", "DC1", "DC2", "DC3", "DC4", "NAK", "SYN", "ETB",
           "CAN", "EM",  "SUB", "ESC", "FS",  "GS",  "RS",  "US"]

    getAt : Nat -> List String -> Maybe String
    getAt Z     (x :: xs) = Just x
    getAt (S k) (x :: xs) = getAt k xs
    getAt _     []        = Nothing

showLitString : List Char -> String -> String
showLitString []        = id
showLitString ('"'::cs) = ("\\\"" ++) . showLitString cs
showLitString (c  ::cs) = (showLitChar c) . showLitString cs

export
Show Char where
  show '\'' = "'\\''"
  show c    = strCons '\'' (showLitChar c "'")

export
Show String where
  show cs = strCons '"' (showLitString (unpack cs) "\"")

export
Show Nat where
  show n = show (the Integer (natToInteger n))

export
Show Bool where
  show True = "True"
  show False = "False"

export
Show () where
  show () = "()"

export
(Show a, Show b) => Show (a, b) where
  show (x, y) = "(" ++ show x ++ ", " ++ show y ++ ")"

export
(Show a, {y : a} -> Show (p y)) => Show (DPair a p) where
    show (y ** prf) = "(" ++ show y ++ " ** " ++ show prf ++ ")"

export
Show a => Show (List a) where
  show xs = "[" ++ show' "" xs ++ "]"
    where
      show' : String -> List a -> String
      show' acc []        = acc
      show' acc [x]       = acc ++ show x
      show' acc (x :: xs) = show' (acc ++ show x ++ ", ") xs

export
Show a => Show (Maybe a) where
  showPrec d Nothing  = "Nothing"
  showPrec d (Just x) = showCon d "Just" (showArg x)

--------
-- IO --
--------

public export
Functor IO where
  map f io = io_bind io (\b => io_pure (f b))

public export
Applicative IO where
  pure x = io_pure x
  f <*> a
      = io_bind f (\f' =>
          io_bind a (\a' =>
            io_pure (f' a')))

public export
Monad IO where
  b >>= k = io_bind b k

export
print : Show a => a -> IO ()
print x = putStr $ show x

export
printLn : Show a => a -> IO ()
printLn x = putStrLn $ show x

-----------------------
-- DOUBLE PRIMITIVES --
-----------------------

public export
pi : Double
pi = 3.14159265358979323846

public export
euler : Double
euler = 2.7182818284590452354

public export
exp : Double -> Double
exp x = prim__doubleExp x

public export
log : Double -> Double
log x = prim__doubleLog x

public export
pow : Double -> Double -> Double
pow x y = exp (y * log x)

public export
sin : Double -> Double
sin x = prim__doubleSin x

public export
cos : Double -> Double
cos x = prim__doubleCos x

public export
tan : Double -> Double
tan x = prim__doubleTan x

public export
asin : Double -> Double
asin x = prim__doubleASin x

public export
acos : Double -> Double
acos x = prim__doubleACos x

public export
atan : Double -> Double
atan x = prim__doubleATan x

public export
sinh : Double -> Double
sinh x = (exp x - exp (-x)) / 2

public export
cosh : Double -> Double
cosh x = (exp x + exp (-x)) / 2

public export
tanh : Double -> Double
tanh x = sinh x / cosh x

public export
sqrt : Double -> Double
sqrt x = prim__doubleSqrt x

public export
floor : Double -> Double
floor x = prim__doubleFloor x

public export
ceiling : Double -> Double
ceiling x = prim__doubleCeiling x

-----------
-- CASTS --
-----------

-- Casts between primitives only here. They might be lossy.

-- To String

public export
interface Cast from to where
  cast : from -> to

export
Cast Int String where
  cast = prim__cast_IntString

export
Cast Integer String where
  cast = prim__cast_IntegerString

export
Cast Char String where
  cast = prim__cast_CharString

export
Cast Double String where
  cast = prim__cast_DoubleString

-- To Integer

export
Cast Int Integer where
  cast = prim__cast_IntInteger

export
Cast Char Integer where
  cast = prim__cast_CharInteger

export
Cast Double Integer where
  cast = prim__cast_DoubleInteger

export
Cast String Integer where
  cast = prim__cast_StringInteger

export
Cast Nat Integer where
  cast = natToInteger

-- To Int

export
Cast Integer Int where
  cast = prim__cast_IntegerInt

export
Cast Char Int where
  cast = prim__cast_CharInt

export
Cast Double Int where
  cast = prim__cast_DoubleInt

export
Cast String Int where
  cast = prim__cast_StringInt

export
Cast Nat Int where
  cast = fromInteger . natToInteger

-- To Char

export
Cast Int Char where
  cast = prim__cast_IntChar

-- To Double

export
Cast Int Double where
  cast = prim__cast_IntDouble

export
Cast Integer Double where
  cast = prim__cast_IntegerDouble

export
Cast String Double where
  cast = prim__cast_StringDouble

export
Cast Nat Double where
  cast = prim__cast_IntegerDouble . natToInteger

------------
-- RANGES --
------------

public export
countFrom : n -> (n -> n) -> Stream n
countFrom start diff = start :: countFrom (diff start) diff

public export
partial
takeUntil : (n -> Bool) -> Stream n -> List n
takeUntil p (x :: xs)
    = if p x
         then [x]
         else x :: takeUntil p xs

partial
takeBefore : (n -> Bool) -> Stream n -> List n
takeBefore p (x :: xs)
    = if p x
         then []
         else x :: takeBefore p xs

public export
interface Range a where
  rangeFromTo : a -> a -> List a
  rangeFromThenTo : a -> a -> a -> List a

  rangeFrom : a -> Stream a
  rangeFromThen : a -> a -> Stream a

-- Idris 1 went to great lengths to prove that these were total. I don't really
-- think it's worth going to those lengths! Let's keep it simple and assert.
export
Range Nat where
  rangeFromTo x y
      = if y > x
           then assert_total $ takeUntil (>= y) (countFrom x S)
           else if x > y
                   then assert_total $ takeUntil (<= y) (countFrom x (\n => minus n 1))
                   else [x]
  rangeFromThenTo x y z
      = if y > x
           then (if z > x
                    then assert_total $ takeBefore (> z) (countFrom x (plus (minus y x)))
                    else [])
           else (if x == y
                    then (if x == z then [x] else [])
                    else assert_total $ takeBefore (< z) (countFrom x (\n => minus n (minus x y))))
  rangeFrom x = countFrom x S
  rangeFromThen x y
      = if y > x
           then countFrom x (plus (minus y x))
           else countFrom x (\n => minus n (minus x y))

export
(Integral a, Ord a, Neg a) => Range a where
  rangeFromTo x y
      = if y > x
           then assert_total $ takeUntil (>= y) (countFrom x (+1))
           else if x > y
                   then assert_total $ takeUntil (<= y) (countFrom x (\x => x-1))
                   else [x]
  rangeFromThenTo x y z
      = if (z - x) > (z - y)
           then -- go up
             assert_total $ takeBefore (> z) (countFrom x (+ (y-x)))
           else if (z - x) < (z - y)
                then -- go down
                     assert_total $ takeBefore (< z) (countFrom x (\n => n - (x - y)))
                else -- meaningless
                  if x == y && y == z
                     then [x] else []
  rangeFrom x = countFrom x (1+)
  rangeFromThen x y
      = if y > x
           then countFrom x (+ (y - x))
           else countFrom x (\n => n - (x - y))

