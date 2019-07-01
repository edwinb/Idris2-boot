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

TODO

Chapter 6
---------

TODO

Chapter 7
---------

TODO

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
