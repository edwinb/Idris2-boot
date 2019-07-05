Type Driven Development with Idris
==================================

The code in the book "Type Driven Development with Idris" by Edwin Brady,
published by Manning, will mostly work in Idris 2, with some small changes
as detailed in this document. The updated code is also [going to be] part
of the test suite (see tests/typedd-book).

Chapter 1
---------

No changes necessary

Chapter 2
---------

The Prelude is smaller than Idris 1, and many functions have been moved to
the base libraries instead. So: 

In `Average.idr`, add:

    import Data.Strings -- for `words`
    import Data.List -- for `length` on lists

In `AveMain.idr` and `Reverse.idr` add:

    import System.REPL -- for 'repl'

Chapter 3
---------

Unbound implicits have multiplicity 0, so we can't match on them at run-time.
Therefore, in `Matrix.idr`, we need to change the type of `createEmpties`
and `transposeMat` so that the length of the inner vector is available to
match on:

    createEmpties : {n : _} -> Vect n (Vect 0 elem)
    transposeMat : {n : _} -> Vect m (Vect n elem) -> Vect n (Vect m elem)

Chapter 4
---------

For the reasons described above:

In `DataStore.idr`, add `import System.REPL` and `import Data.Strings`
In `SumInputs.idr`, add `import System.REPL`
In `TryIndex.idr`, add an implicit argument:

    tryIndex : {n : _} -> Integer -> Vect n a -> Maybe a
    
Chapter 5
---------

There is no longer a `Cast` instance from `String` to `Nat`, because its
behaviour of returing Z if the `String` wasn't numeric was thought to be
confusing. Instead, there is `stringToNatOrZ` in `Data.Strings` which at least
has a clearer name. So:

In `Loops.idr` and `ReadNum.idr` add `import Data.Strings` and change `cast` to
`stringToNatOrZ`

Chapter 6
---------

In `DataStore.idr` and `DataStoreHoles.idr`, add `import Data.Strings` and
`import System.REPL`. Also in `DataStore.idr`, the `schema` argument to
`display` is required for matching, so change the type to:

    display : {schema : _} -> SchemaType schema -> String

In `TypeFuns.idr` add `import Data.Strings`

Chapter 7
---------

`Abs` is now a separate interface from `Neg`. So, change the type of `eval`
to include `Abs` specifically:

    eval : (Abs num, Neg num, Integral num) => Expr num -> num

Also, take `abs` out of the `Neg` implementation for `Expr` and add an
implementation of `Abs` as follows:

    Abs ty => Abs (Expr ty) where
        abs = Abs

Chapter 8
---------

TODO

Chapter 9
---------

TODO

Chapter 10
----------

TODO

Chapter 11
----------

TODO

Chapter 12
----------

TODO

Chapter 13
----------

TODO

Chapter 14
----------

TODO

Chapter 15
----------

TODO
