#include <assert.h>
#include <stdio.h>
#include "idris_net.h"


int main(int argc, char**argv) {
  int eagain = idrnet_geteagain();
  assert(eagain == 35);

  printf("network library tests SUCCESS\n");
  return 0;
}
