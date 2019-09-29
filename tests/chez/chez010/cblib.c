#include <stdio.h>

typedef int(*IntFn)(int, int);

int add(int x, int y) {
    return x+y;
}

int applyIntFn(int x, int y, IntFn f) {
    printf("Callback coming\n");
    return f(x, y);
}

int applyIntFnPure(int x, int y, IntFn f) {
    return f(x, y);
}
