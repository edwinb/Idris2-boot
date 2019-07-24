#include <assert.h>
#include <stdio.h>
#include <netinet/in.h>
#include <arpa/inet.h>

#include "idris_net.h"

void test_eagain() {
  int eagain = idrnet_geteagain();
  assert(eagain == 35);
}


void test_bind_to_0_assigns_random_port() {
  struct sockaddr_in address;
  socklen_t addrlen = sizeof(struct sockaddr);
  int sock = idrnet_socket(AF_INET, 1,  0);
  assert(sock > 0);

  int res = idrnet_bind(sock, AF_INET, 1, "127.0.0.1", 0);
  assert(res == 0);

  res = idrnet_sockaddr_port(sock);
  assert(res > 0);

  printf("socket bound to %d\n",res);
  close(sock);
}


int main(int argc, char**argv) {
  test_eagain();
  test_bind_to_0_assigns_random_port();

  printf("network library tests SUCCESS\n");
  return 0;
}
