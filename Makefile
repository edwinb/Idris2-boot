##### Options which a user might set before building go here #####

PREFIX ?= ${HOME}/.idris2

# Add any optimisation/profiling flags for C here (e.g. -O2)
export OPT=
export CC=clang # clang compiles the output much faster than gcc!

##################################################################

ifeq ($(shell uname -s), Darwin)
	sed_edit_in_place:='-i ""'
else
	sed_edit_in_place:='-i'
endif

# current Idris2 version components
MAJOR=0
MINOR=0
PATCH=0

GIT_SHA1=
VER_TAG=
ifeq ($(shell git status >/dev/null 2>&1; echo $$?), 0)
    # inside a git repo
    ifneq ($(shell git describe --exact-match --tags >/dev/null 2>&1; echo $$?), 0)
        # not tagged as a released version, so add sha1 of this build in between releases
        GIT_SHA1 := $(shell git rev-parse --short=9 HEAD)
        VER_TAG := -${GIT_SHA1}
    endif
endif

IDRIS2_VERSION := ${MAJOR}.${MINOR}.${PATCH}
IDRIS2_VERSION_TAG := ${IDRIS2_VERSION}${VER_TAG}

export IDRIS2_PATH = ${CURDIR}/libs/prelude/build/ttc:${CURDIR}/libs/base/build/ttc:${CURDIR}/libs/network/build/ttc
export IDRIS2_LIBS = ${CURDIR}/libs/network
export IDRIS2_DATA = ${CURDIR}/support

IDRIS_VERSION := $(shell idris --version)
VALID_IDRIS_VERSION_REGEXP = "1.3.2.*"

-include custom.mk

.PHONY: ttimp idris2 idris2-fromc prelude test base clean lib_clean check_version idris2c dist/idris2.c

all: idris2 libs test

# test requires an Idris install! Maybe we should do a version in Idris2?
all-fromc: idris2-fromc libs

check_version:
	@echo "Using Idris 1 version: $(IDRIS_VERSION)"
	@if [ $(shell expr $(IDRIS_VERSION) : $(VALID_IDRIS_VERSION_REGEXP)) -eq 0 ]; then echo "Wrong idris version, expected version matching $(VALID_IDRIS_VERSION_REGEXP)"; exit 1; fi

idris2: dist/idris2.c idris2-fromc

# Just build the C, assuming already built from Idris source.
# Separate rule to avoid having to build the C if Idris 1 isn't available.
# (Also replaces the first line of the generated C with the proper prefix)
#
idris2-fromc:
	sed ${sed_edit_in_place} '1 s|^.*$$|char* idris2_prefix = "${PREFIX}";|' dist/idris2.c
	make -C dist
	@cp dist/idris2 ./idris2

# bit of a hack here, to get the prefix into the generated C!
dist/idris2.c: src/YafflePaths.idr check_version
	@echo "Building Idris 2 version: $(IDRIS2_VERSION_TAG)"
	idris --build idris2.ipkg
	@echo 'char* idris2_prefix = "${PREFIX}";' > idris2_prefix.c
	@echo 'char* getIdris2_prefix() { return idris2_prefix; }' >> idris2_prefix.c
	@cat idris2_prefix.c idris2.c dist/rts/idris_main.c > dist/idris2.c
	@rm -f idris2.c idris2_prefix.c

idris2c: dist/idris2.c
	make -C dist

src/YafflePaths.idr:
	echo 'module YafflePaths; export yversion : ((Nat,Nat,Nat), String); yversion = ((${MAJOR},${MINOR},${PATCH}), "${GIT_SHA1}")' > src/YafflePaths.idr

prelude:
	make -C libs/prelude IDRIS2=../../idris2

base: prelude
	make -C libs/base IDRIS2=../../idris2

network: prelude
	make -C libs/network IDRIS2=../../idris2
	make -C libs/network test IDRIS2=../../idris2

contrib: prelude
	make -C libs/contrib IDRIS2=../../idris2

libs : prelude base network contrib

clean: clean-libs
	make -C src clean
	make -C tests clean
	make -C dist clean
	rm -f runtests
	rm -f idris2 dist/idris2.c

clean-libs:
	make -C libs/prelude clean
	make -C libs/base clean
	make -C libs/network clean
	make -C libs/contrib clean

test:
	idris --build tests.ipkg
	@make -C tests only=$(only)

install-all: install-exec install-support install-libs

install: all install-all

install-fromc: all-fromc install-all

install-support:
	mkdir -p ${PREFIX}/idris2-${IDRIS2_VERSION}/support/chez
	mkdir -p ${PREFIX}/idris2-${IDRIS2_VERSION}/support/chicken
	mkdir -p ${PREFIX}/idris2-${IDRIS2_VERSION}/support/racket
	install support/chez/* ${PREFIX}/idris2-${IDRIS2_VERSION}/support/chez
	install support/chicken/* ${PREFIX}/idris2-${IDRIS2_VERSION}/support/chicken
	install support/racket/* ${PREFIX}/idris2-${IDRIS2_VERSION}/support/racket

install-exec:
	mkdir -p ${PREFIX}/bin
	mkdir -p ${PREFIX}/idris2-${IDRIS2_VERSION}/lib
	install idris2 ${PREFIX}/bin

install-libs: libs
	make -C libs/prelude install IDRIS2=../../idris2
	make -C libs/base install IDRIS2=../../idris2
	make -C libs/network install IDRIS2=../../idris2 IDRIS2_VERSION=${IDRIS2_VERSION}
	make -C libs/contrib install IDRIS2=../../idris2
