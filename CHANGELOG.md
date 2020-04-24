Changes since Idris 2 v0.1.0
----------------------------

Compiler updates:

* Data types with a single constructor, with a single unerased arguments,
  are translated to just that argument, to save repeated packing and unpacking.
  (c.f. `newtype` in Haskell)
* 0-multiplicity constructor arguments are now properly erased, not just
  given a placeholder null value.

Other improvements:

* Various performance improvements in the typechecker:
  + Noting which metavariables are blocking unification constraints, so that
    they only get retried if those metavariables make progress.
  + Evaluating `fromInteger` at compile time.
  + In the run-time, reuse the old heap after garbage collection if it
    hasn't been resized, to avoid unnecessary system calls.

Changes since Idris 1
---------------------

Everything :). For full details, see:
https://idris2.readthedocs.io/en/latest/updates/updates.html
