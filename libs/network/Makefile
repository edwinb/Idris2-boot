RANLIB      ?=ranlib
AR          ?=ar

MACHINE         := $(shell $(CC) -dumpmachine)
ifneq (, $(findstring darwin, $(MACHINE)))
	OS      :=darwin
else ifneq (, $(findstring cygwin, $(MACHINE)))
	OS      :=windows
else ifneq (, $(findstring mingw, $(MACHINE)))
	OS      :=windows
else ifneq (, $(findstring windows, $(MACHINE)))
	OS      :=windows
else
	OS      :=unix
endif

ifeq ($(OS),darwin)
	SHLIB_SUFFIX    :=.dylib
	LIBFLAGS        :=-dynamiclib
else ifeq ($(OS),windows)
	SHLIB_SUFFIX    :=.DLL
	LIBFLAGS        :=-shared
else
	SHLIB_SUFFIX    :=.so
	LIBFLAGS        :=-shared
endif

LIBNAME=idris_net
OBJS = $(LIBNAME).o
HDRS = $(LIBNAME).h
CFLAGS := $(CFLAGS)

ifneq ($(OS), windows)
	CFLAGS += -fPIC
endif

DYLIBTARGET = lib$(LIBNAME)$(SHLIB_SUFFIX)
LIBTARGET = $(LIBNAME).a
TARGET=${HOME}/.idris2

build: $(DYLIBTARGET)
	@if ! [ -d build ]; then echo "creating 'build' directory"; mkdir build ; else echo "directory 'build' exists"; fi
	@if [ -z "${IDRIS2}" ]; then echo 'variable $$IDRIS2 is not set, aborting'; exit 1; fi
	${IDRIS2} --build network.ipkg

$(DYLIBTARGET) : $(OBJS)
	$(CC) -o $(DYLIBTARGET) $(LIBFLAGS) -shared $(OBJS)

install:
	install $(DYLIBTARGET) $(HDRS) $(TARGET)
	${IDRIS2} --install network.ipkg

clean :
	rm -rf $(OBJS) $(LIBTARGET) $(DYLIBTARGET) build

test: $(DYLIBTARGET)
	$(CC) -o network-tests -L. -I. -l$(LIBNAME) test.c
	./network-tests

$(OBJS): $(HDRS)

all: $(DYLIBTARGET) $(LIBTARGET)
	${IDRIS2} --build network.ipkg

.PHONY: build install clean
