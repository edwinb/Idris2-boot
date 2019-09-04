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

SHLIB_SUFFIX    :=.so

LIBNAME=idris_net
OBJS = $(LIBNAME).o
HDRS = $(LIBNAME).h
CFLAGS := $(CFLAGS)
IDRIS_SRCS = Network/Socket.idr Network/Socket/Data.idr Network/Socket/Raw.idr

ifneq ($(OS), windows)
	CFLAGS += -fPIC
endif

DYLIBTARGET = $(LIBNAME)$(SHLIB_SUFFIX)
LIBTARGET = $(LIBNAME).a
TARGET=${HOME}/.idris2

build: $(DYLIBTARGET) $(IDRIS_SRCS)
	@if [ -z "${IDRIS2}" ]; then echo 'variable $$IDRIS2 is not set, aborting'; exit 1; fi
	${IDRIS2} --build network.ipkg

$(DYLIBTARGET) : $(OBJS)
	$(CC) -o $(DYLIBTARGET) $(LIBFLAGS) -shared $(OBJS)

install:
	@if [ -z "${IDRIS2}" ]; then echo 'variable $$IDRIS2 is not set, aborting'; exit 1; fi
	${IDRIS2} --install network.ipkg
	@if ! [ -d $(TARGET)/idris2/network/lib ]; then mkdir $(TARGET)/idris2/network/lib; fi
	install $(DYLIBTARGET) $(HDRS) $(TARGET)/idris2/network/lib

clean :
	rm -rf $(OBJS) $(LIBTARGET) $(DYLIBTARGET) build

test: build test.c
	cp $(DYLIBTARGET) lib$(DYLIBTARGET) # to make C linker happy
	$(CC) -o network-tests -L. -I. test.c -l$(LIBNAME)
	LD_LIBRARY_PATH=. ./network-tests
	./lib-tests

$(OBJS): $(HDRS)

all: $(DYLIBTARGET) $(LIBTARGET)
	${IDRIS2} --build network.ipkg

.PHONY: install clean
