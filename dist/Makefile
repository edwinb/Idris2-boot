.PHONY: idris2 clean

all: idris2

idris2: idris2.c
	make -C rts
	$(CC) idris2.c -o idris2 -I rts -L rts -lidris_rts -lpthread -lgmp -lm

clean:
	make -C rts clean
	rm -f idris2
