Type Driven Development with Idris
==================================

The code in the book "Type Driven Development with Idris" by Edwin Brady,
published by Manning, will mostly work in Idris 2, with some small changes
as detailed in this document. The updated code is also [going to be] part
of the test suite (see tests/typedd).

Chaoter 1
---------

No changes necessary

Chaoter 2
---------

The Prelude is smaller than Idris 1, and many functions have been moved to
the base libraries instead. So: 

In `Average.idr`, add:

    import Data.Strings -- for `words`
    import Data.List -- for `length` on lists

In `AveMain.idr` and `Reverse.idr` add:

    import System.REPL -- for 'repl'

Chaoter 3
---------

Unbound implicits have multiplicity 0, so we can't match on them at run-time.
Therefore, in `Matrix.idr`, we need to change the type of `createEmpties`
and `transposeMat` so that the length of the inner vector is available to
match on:

    createEmpties : {n : _} -> Vect n (Vect 0 elem)
    transposeMat : {n : _} -> Vect m (Vect n elem) -> Vect n (Vect m elem)

Chaoter 4
---------

TODO

Chaoter 5
---------

TODO

Chaoter 6
---------

TODO

Chaoter 7
---------

TODO

Chaoter 8
---------

TODO

Chaoter 9
---------

TODO

Chaoter 10
----------

TODO

Chaoter 11
----------

TODO

Chaoter 12
----------

TODO

Chaoter 13
----------

TODO

Chaoter 14
----------

TODO

Chaoter 15
----------

TODO
