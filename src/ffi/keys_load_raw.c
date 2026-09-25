// Keys.load_raw: adds a raw secret key, 32 bytes of hex, to the table.

#include "bulkhead.h"

Term keys_load_raw_run(Env e, Term* f, IoWork* w) {
  uint64_t n = 0;
  char* hex = io_cstr(e, f[0], &n);
  uint8_t sk[32];
  int bad = bk_unhex(hex, n, sk, 32);
  bk_wipe(hex, n);
  free(hex);
  uint32_t index = 0;
  if (bad) {
    return io_fail(e, EINVAL, "privateKey is not 32 bytes of hex");
  }
  int added = bk_add_key(sk, &index);
  bk_wipe(sk, sizeof(sk));
  if (added != 0) {
    return io_fail(e, EINVAL, "privateKey is not a valid BLS secret key");
  }
  return io_done(e, (Term)index);
}

static void __attribute__((constructor)) keys_load_raw_use(void) {
  io_eff(CID_KEYS_LOAD_RAW, keys_load_raw_run, 0);
}
