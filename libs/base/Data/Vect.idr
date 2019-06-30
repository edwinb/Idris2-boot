module Data.Vect

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
replicate : (len : Nat) -> (x : elem) -> Vect len elem
replicate Z     x = []
replicate (S k) x = x :: replicate k x

