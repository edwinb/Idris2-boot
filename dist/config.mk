include $(IDRIS2_CURDIR)/config.mk

CFLAGS += $(OPT) -std=c99 -pipe -fdata-sections -ffunction-sections -D_POSIX_C_SOURCE=200809L

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
