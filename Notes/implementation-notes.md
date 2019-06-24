Some unsorted notes on aspects of the implementation. Sketchy, and not always
completely up to date, but hopefully give some hints as to what's going on and
some ideas where to look in the code to see how certain features work.

Overview
--------
Core language TT (defined in Core.TT), based on quantitative type theory
(see https://bentnib.org/quantitative-type-theory.html). Binders have
"multiplicities" which are either 0, 1 or unlimited.

Terms are indexed over the names in scope so that we know terms are always well
scoped. Values (i.e. normal forms) are defined in Core.Value as NF;
constructors do not evaluate their arguments until explicitly requested.

Elaborate to TT from a higher level language TTImp (defined in TTImp.TTImp),
which is TT with implicit arguments, local function definitions, case blocks,
as patterns, qualified names with automatic type-directed disambiguation, and
proof search.

Elaboration relies on unification (in Core.Unify), which allows postponing
of unification problems. Essentially works the same way as Agda as described
in Ulf Norell's thesis.

General idea is that high level languages will provide a translation to TT.
In the Idris/ namespace we define the high level syntax for Idris, which
translates to TTImp by desugaring operators, do notation, etc.

TT separates 'Ref' (global user defined names) from 'Meta', which are globally
defined metavariables. For efficiency, metavariables are only substituted into
terms if they have non-0 multiplicity, to preserve sharing as much as possible

There is a separate linearity check after elaboration, which updates types of
holes (and is aware of case blocks).

Where to find things:

* Core/ -- anything related to the core TT, typechecking and unification
* TTImp/ -- anything related to the implicit TT and its elaboration
  * TTImp/Elab/ -- Elaboration state and elaboration of terms 
  * TTImp/Interactive/ -- Interactive editing infrastructure
* Parser/ -- various utilities for parsing and lexing TT and TTImp (and other things)
* Utils/ -- some generally useful utilities
* Idris/ -- anything relating to the high level language, translating to TTImp
  * Idris/Elab/ -- High level construct elaboration machinery (e.g. interfaces)

The Core Type, and Ref
----------------------
Core is a "monad" (not really, for efficiency reasons, at the moment...)
supporting Errors and IO [TODO: Allow restricting to specific IO operations]
The raw syntax is defined by a type RawImp which has a source location at each
node, and any errors in elaboration note the location at the point where the
error occurred.

'Ref' is essentially an IORef. Typically we pass them implicitly and use
labels to disambiguate which one we mean. See Core.Core for their
definition. Again, IORef is for efficiency - even if it would be neater to
use a state monad this turned out to be about 2-3 times faster, so I'm
going with the "ugly" choice...

Context
-------
Core.Context defines all the things needed for TT. Most importantly: Def 
gives definitions of names (case trees, builtins, constructors and
holes, mostly); GlobalDef is a definition with all the other information
about it (type, visibility, totality, etc); Gamma is a context mapping names
to GlobalDef, and 'Defs' is the core data structure with everything needed to
typecheck more definitions.

The main Context type stores definitions in an array, indexed by a "resolved
name id" for fast look up. This means that it also needs to be able to convert
between resolved names and full names.

Since we store names in an array, all the lookup functions need to be in the
Core monad. This also turns out to help with loading checked files (see below).

Laziness
--------
Like Idris 1, laziness is marked in types using Lazy, Delay and Force, or
Inf (instead of Lazy) for codata. Unlike Idris 1, these are language primitives
rather than special purpose names.

TTC format
----------
We can save things to binary if we have an implementation of the TTC interface
for it. See Utils.Binary to see how this is done. It uses a global reference
'Ref Bin Binary' which uses Data.Buffer underneath.

When we load checked TTC files, we don't process the definitions immediately,
but rather store them as a 'ContextEntry', which is either a Binary blob, or
a processed definition. We only process the definitions the first time they
are looked up, since converting Binary to the definition is fairly costly,
and often definitions in an imported file are never used.

Bound Implicits
---------------
The RawImp type has a constructor IBindVar. The first time we encounter an
IBindVar, we record the name as one which will be implicitly bound. At the
end of elaboration, we decide which holes should turn into bound variables
(Pi bound in types, Pattern bound on a LHS, still holes on the RHS) by
looking at the list of names bound as IBindVar, the things they depend on,
and sorting them so that they are bound in dependency order. This happens
in State.getToBind.

Once we know what the bound implicits need to be, we bind them in 
'bindImplicits'. Any application of a hole which stands for a bound implicit
gets turned into a local binding (either Pi or Pat as appropriate, or PLet for
@-patterns).

Unbound Implicits
-----------------
Any name beginning with a lower case letter is considered an unbound implicit.
They are elaborated as holes, which may depend on the initial environment of
the elaboration, and after elaboration they are converted to an implicit pi
binding, with multiplicity 0. So, for example:
```idris
map : {f : _} -> (a -> b) -> f a -> f b
```
becomes
```idris
map : {f : _} -> {0 a : _} -> {0 b : _} -> (a -> b) -> f a -> f b
```

Bindings are ordered according to dependency.  It'll infer any additional
names, e.g. in
```idris
lookup : HasType i xs t -> Env xs -> t
```
...where 'xs' is a Vect n a, it infers bindings for n and a.

(TODO: %auto_implicits directive)

Implicit arguments
------------------
When we encounter an implicit argument ('\_' in the raw syntax, or added when
we elaborate an application and see that there is an implicit needed) we
make a new hole which is a fresh name applied to the current environment,
and return that as the elaborated term. If there's enough information elsewhere
we'll find the definition of the hole by unification.

We never substitute holes in a term during elaboration and rely on normalisation
if we need to look inside it. If there are holes remaining after elaboration of a definition, report an
error (it's okay for a hole in a type as long as it's resolved by the time the
definition is done).

See Elab.App.makeImplicit Elab.App.makeAutoImplicit to see where we add holes
for the implicit arguments in applications.

Elab.App does quite a lot of tricky stuff! In an attempt to help with resolving
ambiguous names and record updates, it will sometimes delay elaboration of an
argument (see App.checkRestApp) so that it can get more information about its
type first.

Core.Unify.solveConstraints revisits all of the currently unsolved holes and
constrained definitions, and tries again to unify any constraints which they
require. It also tries to resolve anything defined by proof search.

Additional type inference
-------------------------
A '?' in a type means "infer this part of the type".  This is distinct from "\_"
in types, which means "I don't care what this is". The distinction is in what
happens when inference fails.  If inference fails for "\_", we implicitly bind a
new name (just like pattern matching on the lhs - i.e. it means match
anything). If inference fails for "?", we leave it as a hole and try to fill it
in later. As a result, we can say:

```idris
foo : Vect Int ?
foo = [1,2,3,4]
```
...and the ? will be inferred to be 4. But if we say

```idris
foo : Vect Int _
foo = [1,2,3,4]
```
...we'll get an error, because the '\_' has been bound as a new name.

So the meaning of "\_" is now consistent on the lhs and in types (i.e. it
means infer a value and bind a variable on failure to infer anything). In
practice, using "\_" will get you the old Idris behaviour, but "?" might get
you a bit more type inference.

Auto Implicits
--------------
Auto implicits are resolved by proof search, and can be given explicit
arguments in the same way as ordinary implicits: i.e. {x = exp} to give
'exp' as the value for auto implicit 'x'. Interfaces are syntactic sugar for
auto implicits (it uses the resolution mechanism - interfaces translate into
records, and implementations translate into hints for the search).

The argument syntax `@{exp}` means that the value of the next auto implicit in
the application should be 'exp' - this is the same as the syntax for invoking
named implementations in Idris 1, but interfaces and auto implicits have been
combined now.

Dot Patterns
------------
IMustUnify is a constructor of RawImp. When we elaborate this, we generate a
hole, then elaborate the term, and add a constraint that the generated hole
must unify with the term which was explicitly given (in UnifyState.addDot),
finally checked in 'UnifyState.checkDots'

Proof Search
------------
A definition with the body 'BySearch' is a hole which will be resolved
by searching for something which fits the type. This happens in
Core.AutoSearch. It checks all possible hints for a term, to ensure that only
one is possible.

@-Patterns
----------
Names which are bound in types are also bound as @-patterns, meaning that
functions have access to them. For example, we can say:

```idris
vlength : Vect n a -> Nat
vlength [] = n
vlength (x :: xs) = n
```

Linear Types
------------
Following Conor McBride and Bob Atkey's work, all binders have a multiplicity
annotation ("RigCount"). After elaboration in TTImp.Elab, we do a separate
linearity check which: a) makes sure that linear variables are used exactly
once; b) updates hole types to properly reflect usage information.

Local definitions
-----------------
We elaborate relative to an environment, meaning that we can elaborate local
function definitions. We keep track of the names being defined in a nested
block of declarations, and ensure that they are lifted to top level definitions
in TT by applying them to every name in scope.

Since we don't know how many times a local definition will be applied, in general,
anything bound with multiplicity 1 is passed to the local definition with
multiplicity 0, so if you want to use it in a local definition, you need to
pass it explicitly.

Case blocks
-----------
Similar to local definitions, these are lifted to top level definitions which
represent the case block, which is immediately applied to the scrutinee of
the case.  The function which defines the block takes as arguments: the entire
current environment (so that it can use any name in scope); any names in
the environment which the scrutinee's type depends on (to support dependent
case, but not counting parameters which are unchanged across the structure).

Parameters
----------
The parameters to a data type are taken to be the arguments which appear,
unchanged, in the same position, everywhere across a data definition.

Erasure
-------
Unbound implicits are given '0' multiplicity, so the rule is now that if you
don't explicitly write it in the type of a function or constructor, the 
argument is erased at run time.

Elaboration and the case tree compiler check ensure that 0-multiplicity
arguments are not inspected in case trees.

Namespaces and name visibility
------------------------------
Same rules mostly apply as in Idris 1. The difference is that visibility is
*per namespace* not *per file* (that is, files have no relevance other except
in that they introduce their own namespace, and in that they allow separate
typechecking).

One effect of this is that when a file defines nested namespaces, the inner
namespace can see what's in the outer namespace, but not vice versa unless
names defined in the inner namespace are explicitly exported. The visibility
modifiers "export", "public export", and "private" control whether the name
can be seen in any other namespace, and it's nothing to do with the file
they're defined in at all.

Records
-------
Records are part of TTImp (rather than the surface language). Elaborating a
record declaration creates a data type and associated projection functions.
Record setters are generated on demand while elaborating TTImp (in
TTImp.Elab.Record). Setters are translated directly to 'case' blocks, which
means that update of dependent fields works as one might expect (i.e. it's safe
as long as all of the fields are updated at the same time consistently).

In TTImp, unlike in Idris 1, records are not implicitly put into their own
namespace, but higher level languages (e.g. Idris itself) can do so explicitly
themselves.
