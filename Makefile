PREFIX = ${HOME}/.idris2
export IDRIS2_PATH = ${CURDIR}/prelude/build:${CURDIR}/base/build
export IDRIS2_DATA = ${CURDIR}/support

.PHONY: ttimp yaffle prelude test base clean lib_clean

all: yaffle test

yaffle: src/YafflePaths.idr
	idris --build yaffle.ipkg

src/YafflePaths.idr:
	echo 'module YafflePaths; export yprefix : String; yprefix = "${PREFIX}"' > src/YafflePaths.idr

#prelude:
#	make -C prelude YAFFLE=../yaffle

#base: prelude
#	make -C base YAFFLE=../yaffle

#libs : prelude base

clean: lib_clean
	make -C src clean
	make -C tests clean
	rm -f runtests
	rm -f yaffle

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
