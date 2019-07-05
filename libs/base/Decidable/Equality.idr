module Decidable.Equality

import Data.Maybe
import Data.Nat

--------------------------------------------------------------------------------
-- Decidable equality
--------------------------------------------------------------------------------

||| Decision procedures for propositional equality
public export
interface DecEq t where
  ||| Decide whether two elements of `t` are propositionally equal
  total decEq : (x1 : t) -> (x2 : t) -> Dec (x1 = x2)

--------------------------------------------------------------------------------
-- Utility lemmas
--------------------------------------------------------------------------------

||| The negation of equality is symmetric (follows from symmetry of equality)
export total 
negEqSym : forall a, b . (a = b -> Void) -> (b = a -> Void)
negEqSym p h = p (sym h)

||| Everything is decidably equal to itself
export total 
decEqSelfIsYes : DecEq a => {x : a} -> decEq x x = Yes Refl
decEqSelfIsYes {x} with (decEq x x)
  decEqSelfIsYes {x} | Yes Refl = Refl
  decEqSelfIsYes {x} | No contra = absurd $ contra Refl

--------------------------------------------------------------------------------
--- Unit
--------------------------------------------------------------------------------

export
implementation DecEq () where
  decEq () () = Yes Refl

--------------------------------------------------------------------------------
-- Booleans
--------------------------------------------------------------------------------
total trueNotFalse : True = False -> Void
trueNotFalse Refl impossible

export
implementation DecEq Bool where
  decEq True  True  = Yes Refl
  decEq False False = Yes Refl
  decEq True  False = No trueNotFalse
  decEq False True  = No (negEqSym trueNotFalse)

--------------------------------------------------------------------------------
-- Nat
--------------------------------------------------------------------------------

total ZnotS : Z = S n -> Void
ZnotS Refl impossible

export
implementation DecEq Nat where
  decEq Z     Z     = Yes Refl
  decEq Z     (S _) = No ZnotS
  decEq (S _) Z     = No (negEqSym ZnotS)
  decEq (S n) (S m) with (decEq n m)
   decEq (S n) (S m) | Yes p = Yes $ cong S p
   decEq (S n) (S m) | No p = No $ \h : (S n = S m) => p $ succInjective n m h

--------------------------------------------------------------------------------
-- Maybe
--------------------------------------------------------------------------------

total nothingNotJust : {x : t} -> (Nothing {ty = t} = Just x) -> Void
nothingNotJust Refl impossible

export
implementation (DecEq t) => DecEq (Maybe t) where
  decEq Nothing Nothing = Yes Refl
  decEq (Just x') (Just y') with (decEq x' y')
    decEq (Just x') (Just y') | Yes p = Yes $ cong Just p
    decEq (Just x') (Just y') | No p 
       = No $ \h : Just x' = Just y' => p $ justInjective h
  decEq Nothing (Just _) = No nothingNotJust
  decEq (Just _) Nothing = No (negEqSym nothingNotJust)

-- TODO: Primitives and other prelude data types



