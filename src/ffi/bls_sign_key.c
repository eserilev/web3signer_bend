// Bls.sign_key: signs a 32-byte root with key index, on a helper thread.
// Returns the compressed signature as 0x hex.

#include "bulkhead.h"

typedef struct {
  uint32_t index;
  byte root[32];
  char out[2 + 192 + 1];
  int ok;
} BkSign;

static void bls_sign_key_call(IoWork* w) {
  BkSign* s = (BkSign*)w->data;
  blst_scalar sk;
  s->ok = bk_get_key(s->index, &sk) == 0;
  if (!s->ok) {
    return;
  }
  blst_p2 hash, sig;
  byte bytes[96];
  blst_hash_to_g2(&hash, s->root, 32, bk_dst, sizeof(bk_dst) - 1, NULL, 0);
  blst_sign_pk_in_g1(&sig, &hash, &sk);
  bk_wipe(&sk, sizeof(sk));
  blst_p2_compress(bytes, &sig);
  bk_hex(bytes, 96, s->out);
}

static Term bls_sign_key_pack(Env e, IoWork* w) {
  BkSign* s = (BkSign*)w->data;
  Term r = s->ok ? io_done(e, io_str(e, s->out, 2 + 192)) : io_fail(e, EINVAL, "no key has this index");
  free(s);
  return r;
}

Term bls_sign_key_run(Env e, Term* f, IoWork* w) {
  BkSign* s = calloc(1, sizeof(BkSign));
  if (s == NULL) {
    return io_fail(e, ENOMEM, NULL);
  }
  uint64_t n = 0;
  char* hex = io_cstr(e, f[1], &n);
  int bad = bk_unhex(hex, n, s->root, 32);
  free(hex);
  if (bad) {
    free(s);
    return io_fail(e, EINVAL, "signing root is not 32 bytes of hex");
  }
  s->index = (uint32_t)f[0];
  w->data = (char*)s;
  return io_work(w, bls_sign_key_call, bls_sign_key_pack);
}

static void __attribute__((constructor)) bls_sign_key_use(void) {
  io_eff(CID_BLS_SIGN_KEY, bls_sign_key_run, 0);
}
