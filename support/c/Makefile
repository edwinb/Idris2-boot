
TARGET = libidris2_support

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

LIBTARGET = $(TARGET).a
DYLIBTARGET = ${TARGET}$(SHLIB_SUFFIX)

CFLAGS := -O2 -Wall -Wextra $(CFLAGS)
LDFLAGS := $(LDFLAGS)

SRCS = $(wildcard *.c)
OBJS = $(SRCS:.c=.o)
DEPS = $(OBJS:.o=.d)


.PHONY: build

build : $(LIBTARGET) $(DYLIBTARGET)

$(LIBTARGET) : $(OBJS)
	ar rc $@ $^
	ranlib $@

$(DYLIBTARGET) : $(OBJS)
	$(CC) -shared ${LDFLAGS} -o $@ $^


-include $(DEPS)

%.d: %.c
	@$(CPP) $(CFLAGS) $< -MM -MT $(@:.d=.o) >$@


.PHONY: clean

clean:
	rm -f $(OBJS) $(DYLIBTARGET) $(LIBTARGET)

cleandep: clean
	rm -f ${DEPS}


.PHONY: install

install: $(LIBTARGET) $(DYLIBTARGET)
	mkdir -p ${PREFIX}/idris2-${IDRIS2_VERSION}/lib
	install $(LIBTARGET) $(DYLIBTARGET) ${PREFIX}/idris2-${IDRIS2_VERSION}/lib
