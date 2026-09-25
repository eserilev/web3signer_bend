// Bls.sign: the phase 0 foreign effect. It takes a secret key and a 32-byte
// signing root as 0x hex strings and returns the compressed G2 signature as
// a 0x hex string. The key bytes are wiped before the effect returns.

#include "blst.h"

static const byte bulkhead_dst[] = "BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_";

static void bulkhead_wipe(void* p, size_t n) {
  volatile unsigned char* v = (volatile unsigned char*)p;
  while (n--) {
    *v++ = 0;
  }
}

static int bulkhead_nibble(char c) {
  if (c >= '0' && c <= '9') return c - '0';
  if (c >= 'a' && c <= 'f') return c - 'a' + 10;
  if (c >= 'A' && c <= 'F') return c - 'A' + 10;
  return -1;
}

static int bulkhead_unhex(const char* s, uint64_t n, byte* out, size_t len) {
  if (n >= 2 && s[0] == '0' && (s[1] == 'x' || s[1] == 'X')) {
    s += 2;
    n -= 2;
  }
  if (n != 2 * len) {
    return -1;
  }
  for (size_t i = 0; i < len; i++) {
    int hi = bulkhead_nibble(s[2 * i]);
    int lo = bulkhead_nibble(s[2 * i + 1]);
    if (hi < 0 || lo < 0) {
      return -1;
    }
    out[i] = (byte)((hi << 4) | lo);
  }
  return 0;
}

Term bls_sign_run(Env e, Term* f, IoWork* w) {
  static const char digits[] = "0123456789abcdef";
  uint64_t sk_n = 0;
  uint64_t root_n = 0;
  char* sk_hex = io_cstr(e, f[0], &sk_n);
  char* root_hex = io_cstr(e, f[1], &root_n);
  byte sk_bytes[32];
  byte root[32];
  int bad_sk = bulkhead_unhex(sk_hex, sk_n, sk_bytes, 32);
  int bad_root = bulkhead_unhex(root_hex, root_n, root, 32);
  bulkhead_wipe(sk_hex, sk_n);
  free(sk_hex);
  free(root_hex);
  if (bad_sk || bad_root) {
    bulkhead_wipe(sk_bytes, sizeof(sk_bytes));
    return io_fail(e, EINVAL, bad_sk ? "bad secret key hex" : "bad signing root hex");
  }

  blst_scalar sk;
  blst_scalar_from_bendian(&sk, sk_bytes);
  bulkhead_wipe(sk_bytes, sizeof(sk_bytes));
  if (!blst_sk_check(&sk)) {
    bulkhead_wipe(&sk, sizeof(sk));
    return io_fail(e, EINVAL, "secret key is zero or not below the group order");
  }

  blst_p2 hash;
  blst_p2 sig;
  byte sig_bytes[96];
  blst_hash_to_g2(&hash, root, sizeof(root), bulkhead_dst, sizeof(bulkhead_dst) - 1, NULL, 0);
  blst_sign_pk_in_g1(&sig, &hash, &sk);
  bulkhead_wipe(&sk, sizeof(sk));
  blst_p2_compress(sig_bytes, &sig);

  char out[2 + 2 * 96];
  out[0] = '0';
  out[1] = 'x';
  for (size_t i = 0; i < 96; i++) {
    out[2 + 2 * i] = digits[sig_bytes[i] >> 4];
    out[3 + 2 * i] = digits[sig_bytes[i] & 15];
  }
  return io_done(e, io_str(e, out, sizeof(out)));
}

static void __attribute__((constructor)) bls_sign_use(void) {
  io_eff(CID_BLS_SIGN, bls_sign_run, 0);
}
