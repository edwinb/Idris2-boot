#include "idris_support.h"
#include <string.h>
#include <errno.h>
#include <time.h>

int idris2_isNull(void* ptr) {
    return (ptr == NULL);
}

char* idris2_getString(void *p) {
    return (char*)p;
}

int idris2_getErrno() {
    return errno;
}

void idris2_sleep(int sec) {
    struct timespec t;
    t.tv_sec = sec;
    t.tv_nsec = 0;

    nanosleep(&t, NULL);
}

void idris2_usleep(int usec) {
    struct timespec t;
    t.tv_sec = usec / 1000000;
    t.tv_nsec = (usec % 1000000) * 1000;

    nanosleep(&t, NULL);
}

int idris2_time() {
    return time(NULL); // RTS needs to have 32 bit integers at least
}
