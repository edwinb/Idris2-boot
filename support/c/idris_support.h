#ifndef __IDRIS_SUPPORT_H
#define __IDRIS_SUPPORT_H

// Return non-zero if the pointer is null
int idris2_isNull(void*);
// Convert a Ptr String intro a String, assuming the string has been checked
// to be non-null
char* idris2_getString(void *p);
int idris2_getErrno();

#endif
