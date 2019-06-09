PREFIX = ${HOME}/.idris2
export IDRIS2_PATH = ${CURDIR}/prelude/build:${CURDIR}/base/build
export IDRIS2_DATA = ${CURDIR}/support

.PHONY: ttimp idris2 prelude test base clean lib_clean

all: idris2 test

idris2: src/YafflePaths.idr
	idris --build idris2.ipkg

src/YafflePaths.idr:
	echo 'module YafflePaths; export yprefix : String; yprefix = "${PREFIX}"' > src/YafflePaths.idr

#prelude:
#	make -C libs/prelude YAFFLE=../../idris2

#base: prelude
#	make -C libs/base YAFFLE=../../idris2

#libs : prelude base

clean: lib_clean
	make -C src clean
	make -C tests clean
	rm -f runtests
	rm -f idris2

lib_clean:
#	make -C prelude clean
#	make -C base clean

test:
	idris --build tests.ipkg
	make -C tests

#install:
#	mkdir -p ${PREFIX}/bin
#	mkdir -p ${PREFIX}/blodwen/support/chez
#	mkdir -p ${PREFIX}/blodwen/support/chicken
#	mkdir -p ${PREFIX}/blodwen/support/racket
#	make -C prelude install BLODWEN=../blodwen
#	make -C base install BLODWEN=../blodwen
#
#	install blodwen ${PREFIX}/bin
#	install support/chez/* ${PREFIX}/blodwen/support/chez
#	install support/chicken/* ${PREFIX}/blodwen/support/chicken
#	install support/racket/* ${PREFIX}/blodwen/support/racket
