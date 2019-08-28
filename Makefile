PREFIX ?= ${HOME}/.idris2
IDRIS_VERSION := $(shell idris --version)
VALID_IDRIS_VERSION_REGEXP = "1.3.2.*"
export IDRIS2_PATH = ${CURDIR}/libs/prelude/build:${CURDIR}/libs/base/build
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
	@echo 'module YafflePaths; export yprefix : String; yprefix = "${PREFIX}"; export yversion : ((Nat,Nat,Nat), String); yversion = ((0,0,0), "")' > src/YafflePaths.idr

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
	mkdir -p ${PREFIX}/idris2/lib
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
	make -C libs/network install IDRIS2=../../idris2
