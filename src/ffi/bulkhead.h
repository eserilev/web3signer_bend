// Shared C code for the foreign effects of Bulkhead. Each effect file
// includes this header; the guard keeps one copy in the generated program.
//
// Secret keys live only here, in bk_keys. Bend code sees a key by its index.

#ifndef BULKHEAD_FFI_H
#define BULKHEAD_FFI_H

#include <arpa/inet.h>
#include <dirent.h>
#include <errno.h>
#include <fcntl.h>
#include <netinet/in.h>
#include <pthread.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <unistd.h>

#include <openssl/evp.h>
#include <openssl/sha.h>
#include <unicode/unorm2.h>
#include <unicode/ustring.h>

#include "blst.h"

static const byte bk_dst[] = "BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_";

static void bk_wipe(void* p, size_t n) {
  volatile unsigned char* v = (volatile unsigned char*)p;
  while (n--) {
    *v++ = 0;
  }
}

static int bk_nibble(char c) {
  if (c >= '0' && c <= '9') return c - '0';
  if (c >= 'a' && c <= 'f') return c - 'a' + 10;
  if (c >= 'A' && c <= 'F') return c - 'A' + 10;
  return -1;
}

// Decodes hex with an optional 0x prefix into a new buffer. Returns 0 on
// success; *out is malloc'ed and holds *len bytes.
static int bk_unhex_alloc(const char* s, size_t n, uint8_t** out, size_t* len) {
  if (n >= 2 && s[0] == '0' && (s[1] == 'x' || s[1] == 'X')) {
    s += 2;
    n -= 2;
  }
  if (n % 2 != 0) {
    return -1;
  }
  uint8_t* b = malloc(n / 2 + 1);
  if (b == NULL) {
    return -1;
  }
  for (size_t i = 0; i < n / 2; i++) {
    int hi = bk_nibble(s[2 * i]);
    int lo = bk_nibble(s[2 * i + 1]);
    if (hi < 0 || lo < 0) {
      free(b);
      return -1;
    }
    b[i] = (uint8_t)((hi << 4) | lo);
  }
  *out = b;
  *len = n / 2;
  return 0;
}

// Decodes hex of exactly len bytes into out.
static int bk_unhex(const char* s, size_t n, uint8_t* out, size_t len) {
  uint8_t* b;
  size_t got;
  if (bk_unhex_alloc(s, n, &b, &got) != 0) {
    return -1;
  }
  int ok = got == len;
  if (ok) {
    memcpy(out, b, len);
  }
  bk_wipe(b, got);
  free(b);
  return ok ? 0 : -1;
}

// Writes "0x" and 2n lowercase hex digits, then a NUL.
static void bk_hex(const uint8_t* in, size_t n, char* out) {
  static const char digits[] = "0123456789abcdef";
  out[0] = '0';
  out[1] = 'x';
  for (size_t i = 0; i < n; i++) {
    out[2 + 2 * i] = digits[in[i] >> 4];
    out[3 + 2 * i] = digits[in[i] & 15];
  }
  out[2 + 2 * n] = 0;
}

// The key table
// =============

static blst_scalar* bk_keys = NULL;
static uint32_t bk_count = 0;
static uint32_t bk_cap = 0;
static pthread_rwlock_t bk_lock = PTHREAD_RWLOCK_INITIALIZER;

// Adds a secret key (32 big-endian bytes). Returns 0 and the index, or -1
// if the key is zero or not below the group order.
static int bk_add_key(const uint8_t sk_be[32], uint32_t* index) {
  blst_scalar sk;
  blst_scalar_from_bendian(&sk, sk_be);
  if (!blst_sk_check(&sk)) {
    bk_wipe(&sk, sizeof(sk));
    return -1;
  }
  pthread_rwlock_wrlock(&bk_lock);
  if (bk_count == bk_cap) {
    uint32_t cap = bk_cap ? bk_cap * 2 : 64;
    blst_scalar* grown = malloc(sizeof(blst_scalar) * cap);
    if (grown == NULL) {
      pthread_rwlock_unlock(&bk_lock);
      bk_wipe(&sk, sizeof(sk));
      return -1;
    }
    if (bk_keys != NULL) {
      memcpy(grown, bk_keys, sizeof(blst_scalar) * bk_count);
      bk_wipe(bk_keys, sizeof(blst_scalar) * bk_cap);
      free(bk_keys);
    }
    bk_keys = grown;
    bk_cap = cap;
  }
  bk_keys[bk_count] = sk;
  *index = bk_count;
  bk_count += 1;
  pthread_rwlock_unlock(&bk_lock);
  bk_wipe(&sk, sizeof(sk));
  return 0;
}

// Copies key index into sk. Returns -1 if there is no such key.
static int bk_get_key(uint32_t index, blst_scalar* sk) {
  pthread_rwlock_rdlock(&bk_lock);
  int ok = index < bk_count;
  if (ok) {
    *sk = bk_keys[index];
  }
  pthread_rwlock_unlock(&bk_lock);
  return ok ? 0 : -1;
}

// Passwords (EIP-2335)
// ====================

// NFKD-normalizes a UTF-8 password and removes the C0 and C1 control
// characters and DEL, as EIP-2335 requires. Returns a malloc'ed UTF-8
// buffer and its length, or NULL.
static char* bk_password(const char* in, size_t n, size_t* out_n) {
  UErrorCode st = U_ZERO_ERROR;
  int32_t len16 = 0;
  u_strFromUTF8(NULL, 0, &len16, in, (int32_t)n, &st);
  if (st != U_BUFFER_OVERFLOW_ERROR && U_FAILURE(st)) {
    return NULL;
  }
  st = U_ZERO_ERROR;
  UChar* src = malloc(sizeof(UChar) * (size_t)(len16 + 1));
  if (src == NULL) {
    return NULL;
  }
  u_strFromUTF8(src, len16 + 1, &len16, in, (int32_t)n, &st);
  const UNormalizer2* nfkd = unorm2_getNFKDInstance(&st);
  int32_t cap = len16 * 18 + 16;
  UChar* dst = malloc(sizeof(UChar) * (size_t)cap);
  if (U_FAILURE(st) || dst == NULL) {
    bk_wipe(src, sizeof(UChar) * (size_t)(len16 + 1));
    free(src);
    free(dst);
    return NULL;
  }
  int32_t dn = unorm2_normalize(nfkd, src, len16, dst, cap, &st);
  bk_wipe(src, sizeof(UChar) * (size_t)(len16 + 1));
  free(src);
  if (U_FAILURE(st)) {
    bk_wipe(dst, sizeof(UChar) * (size_t)cap);
    free(dst);
    return NULL;
  }
  int32_t kept = 0;
  for (int32_t i = 0; i < dn; i++) {
    UChar c = dst[i];
    int control = c <= 0x1F || (c >= 0x7F && c <= 0x9F);
    if (!control) {
      dst[kept++] = c;
    }
  }
  int32_t len8 = 0;
  st = U_ZERO_ERROR;
  u_strToUTF8(NULL, 0, &len8, dst, kept, &st);
  st = U_ZERO_ERROR;
  char* out = malloc((size_t)len8 + 1);
  if (out != NULL) {
    u_strToUTF8(out, len8 + 1, &len8, dst, kept, &st);
  }
  bk_wipe(dst, sizeof(UChar) * (size_t)cap);
  free(dst);
  if (out == NULL || U_FAILURE(st)) {
    free(out);
    return NULL;
  }
  *out_n = (size_t)len8;
  return out;
}

#endif
