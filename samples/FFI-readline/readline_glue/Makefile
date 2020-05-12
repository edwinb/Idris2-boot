
IDRIS := idris2
INSTALLDIR = `${IDRIS} --libdir`/readline/lib

TARGET = libidrisreadline

MACHINE := $(shell $(CC) -dumpmachine)
ifneq (,$(findstring cygwin, $(MACHINE)))
	OS := windows
	SHLIB_SUFFIX := .dll
else ifneq (,$(findstring mingw, $(MACHINE)))
	OS := windows
	SHLIB_SUFFIX := .dll
else ifneq (,$(findstring windows, $(MACHINE)))
	OS := windows
	SHLIB_SUFFIX := .dll
else ifneq (,$(findstring darwin, $(MACHINE)))
	OS := darwin
	SHLIB_SUFFIX := .dylib
	CFLAGS += -fPIC
else
	OS := unix
	SHLIB_SUFFIX := .so
	CFLAGS += -fPIC
endif


CFLAGS := -Wall -Wextra $(CFLAGS)
LDFLAGS := $(LDFLAGS) -lreadline

SRCS = $(wildcard *.c)
OBJS = $(SRCS:.c=.o)
DEPS = $(OBJS:.o=.d)


all: ${TARGET}$(SHLIB_SUFFIX)

$(TARGET)$(SHLIB_SUFFIX): $(OBJS)
	$(CC) -shared ${LDFLAGS} -o $@ $^


-include $(DEPS)

%.d: %.c
	@$(CPP) $(CFLAGS) $< -MM -MT $(@:.d=.o) >$@


.PHONY: clean

clean :
	rm -f $(OBJS) $(TARGET)$(SHLIB_SUFFIX)

cleandep: clean
	rm -f ${DEPS}


.PHONY: install

install:
	@if ! [ -d $(INSTALLDIR) ]; then mkdir -p $(INSTALLDIR); fi
	install $(TARGET)$(SHLIB_SUFFIX) $(wildcard *.h) $(INSTALLDIR)
