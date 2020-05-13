include config.mk

CFLAGS += -Wno-unused-variable -Wno-unused-label

.PHONY: idris2 clean

all: idris2

idris2: idris2.c
	$(MAKE) -C rts
	$(CC) $(CFLAGS) idris2.c -o idris2 -I rts -L rts -lidris_rts $(GMP_LIB_DIR) -lgmp -lm

clean:
	$(MAKE) -C rts clean
	rm -f idris2
