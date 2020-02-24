make -C rts
clang idris2.c -o idris2 -I rts -L rts -lidris_rts -lpthread -lgmp -lm
