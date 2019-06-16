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
  data DPair : (a : Type) -> (a -> Type) -> Type where
       MkDPair : {0 a : Type} -> {0 p : a -> Type} -> 
                 (1 x : a) -> (1 y : p x)-> DPair a p

  public export
  fst : DPair a p -> a
  fst (MkDPair x y) = x

  public export
  snd : (x : DPair a p) -> p (fst x)
  snd (MkDPair x y) = y

-- The empty type

public export
data Void : Type where

-- Equality

public export
data Equal : forall a, b . a -> b -> Type where
     Refl : {0 x : a} -> Equal x x

%name Equal prf

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
