||| Test extended record syntax
data NotZero : Nat -> Type where
  Is : {n : Nat} -> NotZero (S n)

record Positive (n : Nat) {auto 0 pos : NotZero n} where
  constructor Check

a : Positive 1
a = Check

b : Positive 2
b = Check

{- Will not type-check
c : Positive 0
-}
