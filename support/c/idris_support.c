#include "idris_support.h"
#include <string.h>
#include <errno.h>

int idris2_isNull(void* ptr) {
    return (ptr == NULL);
}

char* idris2_getString(void *p) {
    return (char*)p;
}

int idris2_getErrno() {
    return errno;
}
