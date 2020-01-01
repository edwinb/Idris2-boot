module Builtin

-- The most primitive data types; things which are used by desugaring

-- Totality assertions
%inline
public export
assert_total : {0 a : _} -> a -> a
assert_total x = x

%inline
public export
assert_smaller : {0 a, b : _} -> (x : a) -> (y : b) -> b
assert_smaller x y = y

-- Unit type and pairs

public export
data Unit = MkUnit

public export
data Pair : Type -> Type -> Type where
     MkPair : {0 a, b : Type} -> (1 x : a) -> (1 y : b) -> Pair a b

public export
fst : {0 a, b : Type} -> (a, b) -> a
fst (x, y) = x

public export
snd : {0 a, b : Type} -> (a, b) -> b
snd (x, y) = y

-- This directive tells auto implicit search what to use to look inside pairs
%pair Pair fst snd

namespace DPair
  public export
  record DPair a (p : a -> Type) where
    constructor MkDPair
    fst : a
    snd : p fst

-- The empty type

public export
data Void : Type where

-- Equality

public export
data Equal : forall a, b . (0 x : a)  -> (0 y : b) -> Type where
     Refl : {0 x : a} -> Equal x x

%name Equal prf

infix 9 ===, ~=~

-- An equality type for when you want to assert that each side of the
-- equality has the same type, but there's not other evidence available
-- to help with unification
public export
(===) : (0 x : a) -> (0 y : a) -> Type
(===) = Equal

public export
(~=~) : (0 x : a) -> (0 y : b) -> Type
(~=~) = Equal


%inline
public export
rewrite__impl : {0 x, y : a} -> (0 p : _) ->
                (0 rule : x = y) -> (1 val : p y) -> p x
rewrite__impl p Refl prf = prf

%rewrite Equal rewrite__impl

%inline
public export
replace : forall x, y, p . (0 rule : x = y) -> p x -> p y
replace Refl prf = prf

%inline
public export
sym : (0 rule : x = y) -> y = x
sym Refl = Refl

%inline
public export
trans : forall a, b, c . (0 l : a = b) -> (0 r : b = c) -> a = c
trans Refl Refl = Refl

public export
believe_me : a -> b
believe_me = prim__believe_me _ _
