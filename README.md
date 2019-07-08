Idris 2
=======

This is a pre-alpha implementation of Idris 2, the successor to Idris.

Idris 2 is mostly backwards compatible with Idris 1, with some minor
exceptions. The most notable user visible differences, which might cause Idris
1 programs to fail to type check, are:

+ Unbound implicit arguments are always erased, so it is a type error to
  attempt to pattern match on one.
+ Simplified resolution of ambiguous names, which might mean you need to
  explicitly disambiguate more often. As a general rule, Idris 2 will be able
  to disambiguate between names which have different concrete return types
  (such as data constructores), or which have different concrete argument
  types (such as record projections). It may struggle to resolve ambiguities
  if one name requires an interface to be resolved.
+ Minor differences in the meaning of export modifiers `private`, `export`,
  and `public export`, which now refer to visibility of names from other
  *namespaces* rather than visibility from other *files*.
+ Module names must match the filename in which they are defined (unless
  the module's name is "Main").
+ Anything which uses a `%language` pragma in Idris 1 is likely to be different.
  Notably, elaborator reflection will exist, but most likely in a slightly
  different form because the internal details of the elaborator are different.
+ The `Prelude` is much smaller (and easier to replace with an alternative).

Watch this space for more details and the rationale for the changes, as I
get around to writing it...

Summary of new features:

+ A core language based on "Quantitative Type Theory" which allows explicit
  annotation of erased types, and linear types.
+ `let` bindings are now more expressive, and can be used to define pattern
  matching functions locally.
+ Names which are in scope in a type are also always in scope in the body of
  the corresponding definition.
+ Better inference. Holes are global to a source file, rather than local to
  a definition, meaning that some holes can be left in function types to be
  inferred by the type checker. This also gives better inference for the types
  of `case` expressions, and means fewer annotations are needed in interface
  declarations.
+ Better type checker implementation which minimises the need for compile
  time evaluation.
+ New Chez Scheme based back end which both compiles and runs faster than the
  default Idris 1 back end. (Also, optionally, Chicken Scheme and Racket can
  be used as targets).
+ Everything works faster :).

A significant change in the implementation is that there is an intermediate
language `TTImp`, which is essentially a desugared Idris, and is cleanly
separated from the high level language which means it is potentially usable
as a core language for other high level syntaxes.

Installation
============

To build and install what exists of it so far:

+ Optionally, set the `PREFIX` in `Makefile`
+ `make idris2`
+ `make install`

You'll need to set your `PATH` to `$PREFIX/bin`
You may also want to set `IDRIS_CC` to `clang`, since this seems to build
the generated C significantly faster.

Note: If you edit `idris2.ipkg` to use the `opts` with optimisation set
(`--cg-opt -O2`) you'll find it runs about twice as fast, at the cost of
taking a couple of minutes to generate the `idris2` executable.

You can check that building succeeded by running

- `make test`

I make no promises how well this works yet, but you are welcome to have a
play. Good luck :).

Information about external dependencies are presented in [INSTALL.md](INSTALL.md).

Things still missing
====================

+ Some high level syntax, notably numeric ranges
+ 'using' blocks
+ Cumulativity (so we currently have Type : Type! Bear that in mind when you
  think you've proved something :))
+ 'rewrite' doesn't yet work on dependent types
+ Some details of 'with' not yet done (notably recursive with call syntax)
+ Parts of the ide-mode, particularly syntax highlighting
+ Documentation strings and HTML documentation generation
+ ':search' and ':apropos' at the REPL
+ The rest of this "Things still missing" list
