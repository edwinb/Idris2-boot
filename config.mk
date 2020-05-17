##### Options which a user might set before building go here #####

PREFIX ?= $(HOME)/.idris2

# Add any optimisation/profiling flags for C here (e.g. -O2)
OPT =

# Use external GMP library
USE_GMP =

# clang compiles the output much faster than gcc!
CC := clang

##################################################################

RANLIB ?= ranlib
AR ?= ar

CFLAGS := -Wall $(CFLAGS)
LDFLAGS := $(LDFLAGS)


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
else ifneq (, $(findstring bsd, $(MACHINE)))
	OS := bsd
	SHLIB_SUFFIX := .so
	CFLAGS += -fPIC
else
        OS := linux
        SHLIB_SUFFIX := .so
        CFLAGS += -fPIC
endif


ifeq ($(OS),bsd)
	MAKE := gmake
else
	MAKE := make
endif


ifeq ($(OS),bsd)
	GMP_INCLUDE_DIR = -I/usr/local/include
	GMP_LIB_DIR     = -L/usr/local/lib
else ifeq ($(OS),darwin)
	GMP_INCLUDE_DIR =
	GMP_LIB_DIR     =
else ifeq ($(OS),windows)
	GMP_INCLUDE_DIR =
	GMP_LIB_DIR     =
else
	GMP_INCLUDE_DIR =
	GMP_LIB_DIR     =
endif
