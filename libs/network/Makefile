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

OBJS = idris_net.o
HDRS = idris_net.h
CFLAGS := $(CFLAGS)

ifneq ($(OS), windows)
	CFLAGS += -fPIC
endif

DYLIBTARGET = idrnet$(SHLIB_SUFFIX)
LIBTARGET = idrnet.a
TARGET=${HOME}/.idris2

build: $(LIBTARGET) $(DYLIBTARGET)

$(LIBTARGET) : $(OBJS)
	$(AR) rc $(LIBTARGET) $(OBJS)
	$(RANLIB) $(LIBTARGET)

$(DYLIBTARGET) : $(OBJS)
	$(CC) -o $(DYLIBTARGET) $(LIBFLAGS) -shared $(OBJS)

install: build
	install $(LIBTARGET) $(HDRS) $(TARGET)
	${IDRIS2} --install network.ipkg

clean :
	rm -rf $(OBJS) $(LIBTARGET) $(DYLIBTARGET) build

$(OBJS): $(HDRS)

all: $(DYLIBTARGET) $(LIBTARGET)
	${IDRIS2} --build network1.ipkg

.PHONY: build install clean
