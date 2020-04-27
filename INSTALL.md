# Installation

Idris 2 is built using Idris, and provides support for two default code
generation targets: Chez Scheme, and Racket. To build from source, it requires
at least Idris version 1.3.2 (see https://www.idris-lang.org/pages/download.html). You
can also build from the generated C.

## Quick summary:

You need a C compiler (default is clang) and Chez Scheme, and optionally
Idris 1.3.2 to build from source.

* If you have Idris 1.3.2 installed:

    make install

* If not, and the generated C is available in `dist`, you can install directly
  from the generated C:

    make install-fromc

The generated C is available in source distributions. It will not be available
if you have cloned directly from https://github.com/edwinb/Idris2

The above commands will build the executable, build the libraries, run the
tests (if Idris 1 is available), then if all is well, install everything. The
default installation directory is `$HOME/.idris2`. You can change this by
setting the `PREFIX` variable in the `Makefile`.

Other settings you can change in the `Makefile` are:

* `OPT` which sets the optimisation level for compiling the generated C.  Leave
  this blank for Idris 2 to build sooner, or set it to `-O2` for a faster
  Idris 2 compiler. `-O2` takes a few minutes!
* `CC` which sets the C compiler to use. `clang` is the default, but `gcc`
  always works. `clang` generates code faster.

## Idris

There are several sets of instructions on how to install Idris from source and
binary.

+ [Official ipkg installer for macOS](https://www.idris-lang.org/pkgs/idris-current.pkg)
+ [Source build instructions from the Idris GitHub Wiki](https://github.com/idris-lang/Idris-dev/wiki/Installation-Instructions)
+ [Binary installation using Cabal from the Idris Manual](https://idris.readthedocs.io/en/latest/tutorial/starting.html)

## Code Generation Targets

Only one of these is absolutely necessary, and you can type check code even
with none of them installed. The default code generator targets Chez Scheme.

### Chez

Chez Scheme is available to build from source:

+ https://cisco.github.io/ChezScheme/

Many popular package managers will provide a binary distribution for Chez. Note
that homebrew for Mac OS X provides a version without multithreading support, so
Mac OS X users will want to build from source.

**Note**: If you install ChezScheme from source files, building it locally, make sure
you run `./configure --threads` to build multithreading support in.

### Chicken

Chicken scheme offers binary distributions (and source tar balls) from

+ https://code.call-cc.org/

You can find chicken in many package managers.

After installing chicken scheme you may need to install the 'numbers' package.

### Racket

Racket is available from:

+ https://download.racket-lang.org/

The following packages are required in order to run Idris:

- base
- racket-lib
- compiler-lib
- r6rs-lib
- math-lib

These can be installed with `raco setup` and `raco pkg install`.
