Changes since Idris 2 v0.1.0
----------------------------

Compiler updates:

* Data types with a single constructor, with a single unerased arguments,
  are translated to just that argument, to save repeated packing and unpacking.
  (c.f. `newtype` in Haskell)
  + A data type can opt out of this behaviour by specifying `noNewtype` in its
    options list. `noNewtype` allows code generators to apply special handling
    to the generated constructor/deconstructor, for a newtype-like data type,
    that would otherwise be optimised away.
* 0-multiplicity constructor arguments are now properly erased, not just
  given a placeholder null value.

Language extensions:

* To improve error messages, one can use `with NS.name <term>`
  or `with [NS.name1, NS.name2, ...] <term>` to disable disambiguation
  for the given names in `<term>`. Example: `with MyNS.(>>=) do ...`.
* %transform directive, for declaring transformation rules on runtime
  expressions. Transformation rules are automatically added for top level
  implementations of interfaces.
* A %spec flag on functions which allows arguments to be marked for partial
  evaluation, following the rules from "Scrapping Your Inefficient Engine"
  (ICFP 2010, Brady & Hammond)

Library additions:

* Additional file management operations in `base`
* New modules in `contrib` for time (`System.Clock`); JSON (`Language.JSON.*`);
  random numbers (`System.Random`)

Other improvements:

* Various performance improvements in the typechecker:
  + Noting which metavariables are blocking unification constraints, so that
    they only get retried if those metavariables make progress.
  + Evaluating `fromInteger` at compile time.
  + In the run-time, reuse the old heap after garbage collection if it
    hasn't been resized, to avoid unnecessary system calls.

* Extend Idris2's literate mode to support reading Markdown and OrgMode files.
  For more details see: https://idris2.readthedocs.io/en/latest/reference/literate.html

* Fields of records can be accessed (and updated) using the dot syntax,
  such as `r.field1.field2` or `record { field1.field2 = 42 }`.
  For details, see https://idris2.readthedocs.io/en/latest/reference/records.html

Changes since Idris 1
---------------------

Everything :). For full details, see:
https://idris2.readthedocs.io/en/latest/updates/updates.html
