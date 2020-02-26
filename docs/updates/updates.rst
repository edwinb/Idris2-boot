.. _updates-index:

#####################
Changes since Idris 1
#####################

Idris 2 is mostly backwards compatible with Idris 1, with some minor
exceptions. This document describes the changes, approximately in order of
likelihood of encountering them in practice. New features are described at
the end, in Section :ref:`sect-new-features`.

[NOT YET COMPLETE]

.. note::
   The documentation for Idris has been published under the Creative
   Commons CC0 License. As such to the extent possible under law, *The
   Idris Community* has waived all copyright and related or neighboring
   rights to Documentation for Idris.

   More information concerning the CC0 can be found online at: http://creativecommons.org/publicdomain/zero/1.0/

New Core Language: Quantities in Types
======================================

Erasure
-------

Linearity
---------

Prelude and ``base`` libraries
==============================

Prelide is much smaller, things moved to ``base``.

Smaller Changes
===============

Ambiguous Name Resolution
-------------------------

Modules, namespaces and export
------------------------------

Change in visibility rules, and module names must match filenames except
``Main``.

``%language`` pragmas
---------------------

Not moved to Idris 2, any extensions are not implemented.

``let`` bindings
----------------

Now don't compute, and equivalent to ``(\x => e) val``, but see 
:ref:`sect-local-defs` below.

``auto``-implicits and Interfaces
---------------------------------

Now the same thing

Totality and Coverage
---------------------

``%default covering`` is now the default status [Actually still TODO, but
planned soon!]

Build artefacts
---------------

Not really a language change, but a change in the way Idris saves checked
files. All checked modules are now saved in a directory ``build/ttc``, in the
root of the source tree, with the directory structure following the directory
structure of the source.  Executables are placed in ``build/exec``.

.. _sect-new-features:

New features
============

In addition to updating the core to QTT, described above.

.. _sect-local-defs:

Local function definitions
--------------------------

However, Idris no longer attempts to infer types for functions defined in
``where`` blocks, because this was fragile. This may be reinstated, if we can
come up with a good, predictable approach.

Scope of implicit arguments
---------------------------

Better inference
----------------

Holes global to a source file, case works better.

Dependent case
--------------

Record updates
--------------

Dependent record updates now work, as long as all relevant fields are updated
at once.

Generate definition
-------------------

A new feature of the IDE protocol, generating complete definitions from a
type signature.

Chez Scheme target
------------------

Also, optionally, Racket, which itself can compile via Chez scheme. Early
experience shows that both are much faster than the Idris 1 C code generator,
in both compile time and execution time (but we haven't done any formal
study on this yet, so it's just anecdotal evidence).
