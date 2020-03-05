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
TARGET=`${IDRIS2} --libdir`

build: $(DYLIBTARGET) $(IDRIS_SRCS)
	@if [ -z "${IDRIS2}" ]; then echo 'variable $$IDRIS2 is not set, aborting'; exit 1; fi
	${IDRIS2} --build network.ipkg

$(DYLIBTARGET) : $(OBJS)
	$(CC) -o $(DYLIBTARGET) $(LIBFLAGS) -shared $(OBJS)

install:
	@if [ -z "${IDRIS2}" ]; then echo 'variable $$IDRIS2 is not set, aborting'; exit 1; fi
	${IDRIS2} --install network.ipkg
	@if ! [ -d $(TARGET)/network/lib ]; then mkdir $(TARGET)/network/lib; fi
	install $(DYLIBTARGET) $(HDRS) $(TARGET)/network/lib

clean :
	rm -rf $(OBJS) $(LIBTARGET) $(DYLIBTARGET) build

test: build test.c
	$(CC) -o network-tests -L. -I. test.c $(DYLIBTARGET)
	LD_LIBRARY_PATH=. ./network-tests
	@rm -f ./network-tests
	./lib-tests

$(OBJS): $(HDRS)

all: $(DYLIBTARGET) $(LIBTARGET)
	${IDRIS2} --build network.ipkg

.PHONY: install clean
