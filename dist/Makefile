include ../config.mk

CFLAGS += $(OPT) -std=c99 -pipe -fdata-sections -ffunction-sections
CFLAGS += -Wno-unused-variable -Wno-unused-label -D_POSIX_C_SOURCE=200809L

ifdef USE_GMP
	LDFLAGS += -lgmp
endif


.PHONY: idris2 clean

all: idris2

idris2: idris2.c
	$(MAKE) -C rts
	$(CC) $(CFLAGS) idris2.c -o idris2 -I rts -L rts -lidris_rts $(GMP_LIB_DIR) $(LDFLAGS) -lm

clean:
	$(MAKE) -C rts clean
	rm -f idris2
