IDE protocol, version 2
=======================

The IDE protocol is (or rather, will be) compatible with the IDE protocol for
Idris 1, as described here:
https://idris.readthedocs.io/en/latest/reference/ide-protocol.html

On start up, it reports:

`000018(:protocol-version 2 0)`

So far, there are two extended commands and one new command.

Extended commands
-----------------

`(:type-of STRING LINE COLUMN)`

If `type-of` is given a line and a column, this looks up the type of the name
at that location, which may be a local variable or a specialisation of a
global definition.

`(:proof-search LINE NAME HINTS :all)`

The optional additional argument `:all` means that the expression search will
return all of the results it finds, one per line (up to a currently hard coded
search depth limit, which will probably be settable as an option in the
future).

`(:case-split LINE COLUMN NAME)`

Case splitting can take an optional additional `COLUMN` argument.

New commands
------------

`(:generate-def LINE NAME)`

Generates a pattern matching definition, if it can find one, for the function
declared with the given name, on the given line. It will only return the
first definition it finds, as a list of pattern clauses. This works via a
combination of case splitting and expression search.
