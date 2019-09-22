# current Idris2 version components
MAJOR=0
MINOR=0
PATCH=0
IDRIS2_VERSION=${MAJOR}.${MINOR}.${PATCH}
PREFIX ?= ${HOME}/.idris2
IDRIS_VERSION := $(shell idris --version)
VALID_IDRIS_VERSION_REGEXP = "1.3.2.*"
export IDRIS2_PATH = ${CURDIR}/libs/prelude/build/ttc:${CURDIR}/libs/base/build/ttc
export IDRIS2_DATA = ${CURDIR}/support

-include custom.mk

.PHONY: ttimp idris2 prelude test base clean lib_clean check_version

all: idris2 libs test

check_version:
	@echo "Using idris version: $(IDRIS_VERSION)"
	@if [ $(shell expr $(IDRIS_VERSION) : $(VALID_IDRIS_VERSION_REGEXP)) -eq 0 ]; then echo "Wrong idris version, expected version matching $(VALID_IDRIS_VERSION_REGEXP)"; exit 1; fi

idris2: src/YafflePaths.idr check_version
	idris --build idris2.ipkg

src/YafflePaths.idr:
	echo 'module YafflePaths; export yversion : ((Nat,Nat,Nat), String); yversion = ((${MAJOR},${MINOR},${PATCH}), "")' > src/YafflePaths.idr
	echo 'export yprefix : String; yprefix = "${PREFIX}"' >> src/YafflePaths.idr

prelude:
	make -C libs/prelude IDRIS2=../../idris2

base: prelude
	make -C libs/base IDRIS2=../../idris2

network: prelude
	make -C libs/network IDRIS2=../../idris2
	make -C libs/network test IDRIS2=../../idris2

libs : prelude base network

clean: clean-libs
	make -C src clean
	make -C tests clean
	rm -f runtests
	rm -f idris2

clean-libs:
	make -C libs/prelude clean
	make -C libs/base clean
	make -C libs/network clean

test:
	idris --build tests.ipkg
	@make -C tests only=$(only)

install: all install-exec install-libs

install-exec: idris2
	mkdir -p ${PREFIX}/bin
	mkdir -p ${PREFIX}/idris2-${IDRIS2_VERSION}/lib
	mkdir -p ${PREFIX}/idris2-${IDRIS2_VERSION}/support/chez
	mkdir -p ${PREFIX}/idris2-${IDRIS2_VERSION}/support/chicken
	mkdir -p ${PREFIX}/idris2-${IDRIS2_VERSION}/support/racket
	install idris2 ${PREFIX}/bin
	install support/chez/* ${PREFIX}/idris2-${IDRIS2_VERSION}/support/chez
	install support/chicken/* ${PREFIX}/idris2-${IDRIS2_VERSION}/support/chicken
	install support/racket/* ${PREFIX}/idris2-${IDRIS2_VERSION}/support/racket

install-libs: libs
	make -C libs/prelude install IDRIS2=../../idris2
	make -C libs/base install IDRIS2=../../idris2
	make -C libs/network install IDRIS2=../../idris2 IDRIS2_VERSION=${IDRIS2_VERSION}
