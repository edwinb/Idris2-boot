IDRIS           := idris2
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

ifeq ($(OS), darwin)
        SHLIB_SUFFIX    :=dylib
else ifeq ($(OS), windows)
        SHLIB_SUFFIX    :=dll
else
        SHLIB_SUFFIX    :=so
endif

LIBTARGET = libidrisreadline.$(SHLIB_SUFFIX)
INSTALLDIR = `${IDRIS} --libdir`/readline/lib

HDRS = idris_readline.h
OBJS = idris_readline.o

READLINE_LIBS := -lreadline
READLINE_FLAGS := -fPIC

CFLAGS = $(READLINE_FLAGS)

$(LIBTARGET): $(OBJS)
	$(CC) -o $(LIBTARGET) -shared $(OBJS) $(READLINE_LIBS) $(READLINE_FLAGS)
	
install:
	@if ! [ -d $(INSTALLDIR) ]; then mkdir -p $(INSTALLDIR); fi
	install $(LIBTARGET) $(HDRS) $(INSTALLDIR)
clean:
	rm $(OBJS) $(LIBTARGET)

.PHONY: install clean
