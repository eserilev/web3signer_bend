// Net.listen: listens on one IPv4 address. TCP.listen in Base always binds
// 0.0.0.0; a signer with no TLS must bind 127.0.0.1 unless told otherwise.

#include "bulkhead.h"

Term net_listen_run(Env e, Term* f, IoWork* w) {
  uint64_t n = 0;
  char* host = io_cstr(e, f[0], &n);
  struct sockaddr_in at;
  memset(&at, 0, sizeof(at));
  at.sin_family = AF_INET;
  at.sin_port = htons((uint16_t)(uint32_t)f[1]);
  int ok = !io_nul(host, n) && inet_pton(AF_INET, host, &at.sin_addr) == 1;
  free(host);
  if (!ok) {
    return io_fail(e, EINVAL, "listen host is not an IPv4 address");
  }
  int fd = socket(AF_INET, SOCK_STREAM, 0);
  if (fd < 0) {
    return io_fail(e, (u32)errno, NULL);
  }
  int one = 1;
  setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &one, sizeof(one));
  if (bind(fd, (struct sockaddr*)&at, sizeof(at)) < 0 || listen(fd, 128) < 0
      || fcntl(fd, F_SETFL, fcntl(fd, F_GETFL) | O_NONBLOCK) < 0) {
    u32 code = (u32)errno;
    close(fd);
    return io_fail(e, code, NULL);
  }
  return io_done(e, io_hand(fd));
}

static void __attribute__((constructor)) net_listen_use(void) {
  io_eff(CID_NET_LISTEN, net_listen_run, 0);
}
