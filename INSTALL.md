# Installation

Idris 2 is built using Idris, and provides support for three default code
generation targets: Chez, Chicken, and Racket. It currently requires the
(not yet released) latest Idris master.

## Idris

There are several sets of instructions on how to install Idris from source and
binary.

+ [Official ipkg installer for macOS](http://www.idris-lang.org/pkgs/idris-current.pkg)
+ [Source build instructions from the Idris GitHub Wiki](https://github.com/idris-lang/Idris-dev/wiki/Installation-Instructions)
+ [Binary installation using Cabal from the Idris Manual](https://idris.readthedocs.io/en/latest/tutorial/starting.html)

## Code Generation Targets

Only one of these is absolutely necessary, and you can type check code even
with none of them installed. The default code generator targets Chez Scheme.

### Chez

Chez Scheme is available to build from source:

+ https://cisco.github.io/ChezScheme/

Many popular package managers will provide a binary distribution for Chez.

### Chicken

Chicken scheme offers binary distributions (and source tar balls) from

+ https://code.call-cc.org/

You can find chicken in many a package manager.

After installing chicken scheme you may need to install the 'numbers' package.

### Racket

Racket is available from:

+ https://download.racket-lang.org/
