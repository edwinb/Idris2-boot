.. _sect-starting:

***************
Getting Started
***************

[NOT UPDATED FOR IDRIS 2 YET]

Prerequisites
=============

[NEEDS UPDATING BEFORE 0.1.0 RELEASE.
Cover Chez Scheme as a default target, and future plans for multiple back ends.]

Before installing Idris, you will need to make sure you have all
of the necessary libraries and tools. You will need:

- A fairly recent version of `GHC <https://www.haskell.org/ghc/>`_. The
  earliest version we currently test with is 7.10.3.

- The *GNU Multiple Precision Arithmetic Library* (GMP) is available  from MacPorts/Homebrew and all major Linux distributions.

Downloading and Installing
==========================

[NEEDS UPDATING BEFORE 0.1.0 RELEASE]

The easiest way to install Idris, if you have all of the
prerequisites, is to type:

::

    cabal update; cabal install idris

This will install the latest version released on Hackage, along with
any dependencies. If, however, you would like the most up to date
development version you can find it, as well as build instructions, on
GitHub at: https://github.com/idris-lang/Idris-dev.

If you haven't previously installed anything using Cabal, then Idris
may not be on your path. Should the Idris executable not be found
please ensure that you have added ``~/.cabal/bin`` to your ``$PATH``
environment variable. Mac OS X users may find they need to add
``~/Library/Haskell/bin`` instead, and Windows users will typically
find that Cabal installs programs in ``%HOME%\AppData\Roaming\cabal\bin``.

To check that installation has succeeded, and to write your first
Idris program, create a file called ``hello.idr`` containing the
following text:

.. code-block:: idris

    module Main

    main : IO ()
    main = putStrLn "Hello world"

If you are familiar with Haskell, it should be fairly clear what the
program is doing and how it works, but if not, we will explain the
details later. You can compile the program to an executable by
entering ``idris hello.idr -o hello`` at the shell prompt. This will,
by default, create a Chez Scheme executable called ``hello.so``, in the
destination directory ``build/exec'' which you can run:

::

    $ idris2 hello.idr -o hello
    compiling hello.ss with output to hello.so
    $ ./build/exec/hello.so
    Hello world

Please note that the dollar sign ``$`` indicates the shell prompt!
Some useful options to the Idris command are:

- ``-o prog`` to compile to an executable called ``prog``.

- ``--check`` type check the file and its dependencies without starting the interactive environment.

- ``--package pkg`` add package as dependency, e.g. ``--package contrib`` to make use of the contrib package.

- ``--help`` display usage summary and command line options.

The Interactive Environment
===========================

[NEED :? BEFORE RELEASE]

Entering ``idris2`` at the shell prompt starts up the interactive
environment. You should see something like the following:

.. literalinclude:: ../listing/idris-prompt-start.txt

This gives a ``ghci`` style interface which allows evaluation of, as
well as type checking of, expressions; theorem proving, compilation;
editing; and various other operations. The command ``:?`` gives a list
of supported commands. Below, we see an example run in
which ``hello.idr`` is loaded, the type of ``main`` is checked and
then the program is compiled to the Chez scheme executable ``hello.so``,
available in the destination directory ``build/exec/''. Type
checking a file, if successful, creates a bytecode version of the file (in this
case ``build/ttc/hello.ttc``) to speed up loading in future. The bytecode is
regenerated if the source file changes.

.. _run1:
.. literalinclude:: ../listing/idris-prompt-helloworld.txt
