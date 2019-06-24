Contributing to Idris 2
=======================

Contributions are welcome! The most important things needed at this stage,
beyond work on the language core, are (in no particular order):

* CI integration.
* Documentation string support (at the REPL and IDE mode).
* A better REPL, including:
  - readline and tab completion
  - :search and :apropos
  - help commands
* Further library support (please add initially into contrib/)
* Partial evaluation, especially for specialisation of interface 
  implementations.
* An alternative, high performance, back end. OCaml seems worth a try.

Some language extensions from Idris 1 have not yet been implemented. Most
notably:

* Type providers
  - Perhaps consider safety - do we allow arbitrary IO operations, or is
    there a way to restrict them so that they can't, for example, delete
    files or run executables.
* Elaborator reflection
  - This will necessarily be slightly different from Idris 1 since the
    elaborator works differently. It would also be nice to extend it with
    libraries and perhaps syntax for deriving implementations of interfaces.

Other contributions are also welcome, but I (@edwinb) will need to be
confident that I'll be able to maintain them!

Some syntax that hasn't yet been implemented but will be:

* Range syntax (e.g. [1..10], [1,3..10], [1..] etc) [needs some thought about
  what should go in the Prelude and exactly how to implement]
* Idiom brackets
* !-notation [needs some thought about the exact rules]

Some things from Idris 1 definitely won't be implemented:

* Uniqueness types (instead, Idris 2 is based on QTT and supports linearity)
* Some esoteric syntax experiments, such as match applications
