Changes since Idris 2 v0.1.0
----------------------------

Compiler updates:

* Data types with a single constructor, with a single unerased arguments,
  are translated to just that argument, to save repeated packing and unpacking.
  (c.f. `newtype` in Haskell)

* Fields of records can be accessed (and updated) using the dot syntax,
  such as `r.field1.field2` or `record { field1.field2 = 42 }`.
  For details, see https://idris2.readthedocs.io/en/latest/reference/records.html

Changes since Idris 1
---------------------

Everything :). For full details, see:
https://idris2.readthedocs.io/en/latest/updates/updates.html
