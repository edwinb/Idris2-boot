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

+ In `DataStore.idr`, add `import System.REPL` and `import Data.Strings`
+ In `SumInputs.idr`, add `import System.REPL`
+ In `TryIndex.idr`, add an implicit argument:

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

In `AppendVec.idr`, add `import Data.Nat` for the `Nat` proofs

`cong` now takes an explicit argument for the function to apply. So, in
`CheckEqMaybe.idr` change the last case to:

    checkEqNat (S k) (S j) = case checkEqNat k j of
                                  Nothing => Nothing
                                  Just prf => Just (cong S prf)

A similar change is necessary in `CheckEqDec.idr`.

In `ExactLength.idr`, the `m` argument to `exactLength` is needed at run time,
so change its type to:

    exactLength : {m : _} ->
                  (len : Nat) -> (input : Vect m a) -> Maybe (Vect len a)

A similar change is necessary in `ExactLengthDec.idr`. Also, `DecEq` is no
longer part of the prelude, so add `import Decidable.Equality`.

In `ReverseVec.idr`, add `import Data.Nat` for the `Nat` proofs.

Chapter 9
---------

+ In `ElemType.idr`, add `import Decidable.Equality`

In `Hangman.idr`:

+ Add `import Decidable.Equality` and `import Data.Strings`
+ `guesses` and `letters` are implicit arguments to `game`, but are used by the
  definition, so add them to its type:

    game : {guesses : _} -> {letters : _} ->
           WordState (S guesses) (S letters) -> IO Finished
  
Chapter 10
----------

Lots of changes necessary here, at least when constructing views, due to Idris
2 having a better (that is, more precise and correct!) implementation of
unification, and the rules for recursive `with` application being tightened up.

In `MergeSort.idr`, add `import Data.List`

In `MergeSortView.idr`, add `import Data.List`, and make the arguments to the
views explicit:

    mergeSort : Ord a => List a -> List a
    mergeSort input with (splitRec input)
      mergeSort [] | SplitRecNil = []
      mergeSort [x] | SplitRecOne x = [x]
      mergeSort (lefts ++ rights) | (SplitRecPair lefts rights lrec rrec)
           = merge (mergeSort lefts | lrec)
                   (mergeSort rights | rrec)

In `SnocList.idr`, in `my_reverse`, the link between `Snoc rec` and `xs ++ [x]`
needs to be made explicit. Idris 1 would happily decide that `xs` and `x` were
the relevant implicit arguments to `Snoc` but this was little more than a guess
based on what would make it type check, whereas Idris 2 is more precise in
what it allows to unify. So, `x` and `xs` need to be explicit arguments to
`Snoc`:

    data SnocList : List a -> Type where
         Empty : SnocList []
         Snoc : (x, xs : _) -> (rec : SnocList xs) -> SnocList (xs ++ [x])
  
Correspondingly, they need to be explicit when matching. For example:

      my_reverse : List a -> List a
      my_reverse input with (snocList input)
        my_reverse [] | Empty = []
        my_reverse (xs ++ [x]) | (Snoc x xs rec) = x :: my_reverse xs | rec

Similar changes are necessary in `snocListHelp` and `my_reverse_help`. See
tests/typedd-book/chapter10/SnocList.idr for the full details.

Also, in `snocListHelp`, `input` is used at run time so needs to be bound
in the type:

    snocListHelp : {input : _} ->
                   (snoc : SnocList input) -> (rest : List a) -> SnocList (input +

It's no longer necessary to give `{input}` explicitly in the patterns for
`snocListHelp`, although it's harmless to do so.

In `IsSuffix.idr`, the matching has to be written slightly differently. The
recursive with application in Idris 1 probably shouldn't have allowed this!

    isSuffix : Eq a => List a -> List a -> Bool
    isSuffix input1 input2 with (snocList input1, snocList input2)
      isSuffix [] input2 | (Empty, s) = True
      isSuffix input1 [] | (s, Empty) = False
      isSuffix (xs ++ [x]) (ys ++ [y]) | (Snoc xsrec, Snoc ysrec)
         = if x == y 
              then isSuffix xs ys | (xsrec, ysrec)
              else False

This doesn't yet get past the totality checker, however, because it doesn't
know about looking inside pairs.

In `DataStore.idr`: Well this is embarrassing - I've no idea how Idris 1 lets
this through! I think perhaps it's too "helpful" when solving unification
problems. To fix it, add an extra parameter `scheme` to `StoreView`, and change
the type of `SNil` to be explicit that the `empty` is the function defined in
`DataStore`. Also add `entry` and `store` as explicit arguments to `SAdd`:

    data StoreView : (schema : _) -> DataStore schema -> Type where
         SNil : StoreView schema DataStore.empty
         SAdd : (entry, store : _) -> (rec : StoreView schema store) ->
                StoreView schema (addToStore entry store)

Since `size` is as explicit argument in the `DataStore` record, it also needs
to be relevant in the type of `storeViewHelp`:

    storeViewHelp : {size : _} ->
                    (items : Vect size (SchemaType schema)) ->
                    StoreView schema (MkData size items)

In `TestStore.idr`:

+ In `listItems`, `empty` needs to be `DataStore.empty` to be explicit that you
  mean the function
+ In `filterKeys`, there is an error in the `SNil` case, which wasn't caught
  because of the type of `SNil` above. It should be:

      filterKeys test DataStore.empty | SNil = []

Chapter 11
----------

Remove `%default total` throughout - it's not yet implemented.

In `Streams.idr` add `import Data.Stream` for `iterate`.

In `Arith.idr` and `ArithTotal.idr`, the `Divides` view now has explicit
arguments for the dividend and remainder, so they need to be explicit in
`bound`:

    bound : Int -> Int
    bound x with (divides x 12)
      bound ((12 * div) + rem) | (DivBy div rem prf) = rem + 1

In `ArithCmd.idr`, update `DivBy` as above. Also add `import Data.Strings` for
`Strings.toLower`.

In `ArithCmd.idr`, update `DivBy` and `import Data.Strings` as above. Also,
since export rules are per-namespace now, rather than per-file, you need to
export `(>>=)` from the namespaces `CommandDo` and `ConsoleDo`.

Chapter 12
----------

Remove `%default total` throughout, at least until it's implemented.

For reasons described above: In `ArithState.idr`, add `import Data.Strings`.
Also the `(>>=)` operators need to be set as `export` since they are in their
own namespaces, and in `getRandom`, `DivBy` needs to take additional
arguments `div` and `rem`.

Chapter 13
----------

TODO

Chapter 14
----------

TODO

Chapter 15
----------

TODO
