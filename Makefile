PREFIX ?= ${HOME}/.idris2
export IDRIS2_PATH = ${CURDIR}/libs/prelude/build:${CURDIR}/libs/base/build
export IDRIS2_DATA = ${CURDIR}/support

-include custom.mk

.PHONY: ttimp idris2 prelude test base clean lib_clean

all: idris2 libs test

idris2: src/YafflePaths.idr
	idris --build idris2.ipkg

src/YafflePaths.idr:
	echo 'module YafflePaths; export yprefix : String; yprefix = "${PREFIX}"' > src/YafflePaths.idr

prelude:
	make -C libs/prelude IDRIS2=../../idris2

base: prelude
	make -C libs/base IDRIS2=../../idris2

libs : prelude base

clean: clean-libs
	make -C src clean
	make -C tests clean
	rm -f runtests
	rm -f idris2

clean-libs:
	make -C libs/prelude clean
	make -C libs/base clean

test:
	idris --build tests.ipkg
	make -C tests

install: all install-exec install-libs

install-exec: idris2
	mkdir -p ${PREFIX}/bin
	mkdir -p ${PREFIX}/idris2/support/chez
	mkdir -p ${PREFIX}/idris2/support/chicken
	mkdir -p ${PREFIX}/idris2/support/racket
	install idris2 ${PREFIX}/bin
	install support/chez/* ${PREFIX}/idris2/support/chez
	install support/chicken/* ${PREFIX}/idris2/support/chicken
	install support/racket/* ${PREFIX}/idris2/support/racket

install-libs: libs
	make -C libs/prelude install IDRIS2=../../idris2
	make -C libs/base install IDRIS2=../../idris2
