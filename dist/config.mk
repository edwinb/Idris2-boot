RANLIB ?=ranlib
CFLAGS :=-O2 -Wall -std=c99 -pipe -fdata-sections -ffunction-sections -D_POSIX_C_SOURCE=200809L $(CFLAGS)

ifeq ($(OS),bsd)
	GMP_INCLUDE_DIR =-I/usr/local/include
	GMP_LIB_DIR     =-L/usr/local/lib
	SHLIB_SUFFIX    =.so
else ifeq ($(OS),darwin)
	GMP_INCLUDE_DIR =
	GMP_LIB_DIR     =
	SHLIB_SUFFIX    =.dylib
else ifeq ($(OS),windows)
	GMP_INCLUDE_DIR =
	GMP_LIB_DIR     =
	SHLIB_SUFFIX    =.DLL
else
	GMP_INCLUDE_DIR =
	GMP_LIB_DIR     =
	SHLIB_SUFFIX    =.so
endif
