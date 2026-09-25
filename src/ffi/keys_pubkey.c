// Keys.pubkey: the compressed public key of key index, as 0x hex.

#include "bulkhead.h"

Term keys_pubkey_run(Env e, Term* f, IoWork* w) {
  blst_scalar sk;
  if (bk_get_key((uint32_t)f[0], &sk) != 0) {
    return io_fail(e, EINVAL, "no key has this index");
  }
  blst_p1 pk;
  byte out[48];
  char hex[2 + 96 + 1];
  blst_sk_to_pk_in_g1(&pk, &sk);
  bk_wipe(&sk, sizeof(sk));
  blst_p1_compress(out, &pk);
  bk_hex(out, 48, hex);
  return io_done(e, io_str(e, hex, 2 + 96));
}

static void __attribute__((constructor)) keys_pubkey_use(void) {
  io_eff(CID_KEYS_PUBKEY, keys_pubkey_run, 0);
}
