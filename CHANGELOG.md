Changes since Idris 2 v0.1.0
----------------------------

Compiler updates:

* Data types with a single constructor, with a single unerased arguments,
  are translated to just that argument, to save repeated packing and unpacking.
  (c.f. `newtype` in Haskell)

* Extend Idris2's literate mode to support reading Markdown and OrgMode files.
  For more details see: https://idris2.readthedocs.io/en/latest/reference/literate.html

Changes since Idris 1
---------------------

Everything :). For full details, see:
https://idris2.readthedocs.io/en/latest/updates/updates.html
