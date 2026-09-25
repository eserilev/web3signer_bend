// Keys.decrypt: decrypts an EIP-2335 keystore and adds the key to the table.
// The KDF runs on a helper thread: scrypt with n = 2^18 takes about a second.

#include "bulkhead.h"

typedef struct {
  int scrypt;
  uint32_t dklen, n, r, p;
  char *salt, *checksum, *cipher, *iv, *password;
  uint64_t salt_n, checksum_n, cipher_n, iv_n, password_n;
  uint32_t index;
  const char* error;
} BkDecrypt;

static void keys_decrypt_free(BkDecrypt* d) {
  bk_wipe(d->password, d->password_n);
  free(d->salt);
  free(d->checksum);
  free(d->cipher);
  free(d->iv);
  free(d->password);
  free(d);
}

static void keys_decrypt_call(IoWork* w) {
  BkDecrypt* d = (BkDecrypt*)w->data;
  uint8_t *salt = NULL, *cipher = NULL;
  size_t salt_len = 0, cipher_len = 0;
  uint8_t checksum[32], iv[16], dk[32], secret[32];
  size_t pw_len = 0;
  char* pw = NULL;
  d->error = NULL;
  if (d->dklen != 32) {
    d->error = "keystore dklen must be 32";
  } else if (bk_unhex_alloc(d->salt, d->salt_n, &salt, &salt_len) != 0) {
    d->error = "keystore salt is not hex";
  } else if (bk_unhex(d->checksum, d->checksum_n, checksum, 32) != 0) {
    d->error = "keystore checksum is not 32 bytes of hex";
  } else if (bk_unhex(d->iv, d->iv_n, iv, 16) != 0) {
    d->error = "keystore iv is not 16 bytes of hex";
  } else if (bk_unhex_alloc(d->cipher, d->cipher_n, &cipher, &cipher_len) != 0 || cipher_len != 32) {
    d->error = "keystore cipher message is not 32 bytes of hex";
  } else if ((pw = bk_password(d->password, d->password_n, &pw_len)) == NULL) {
    d->error = "keystore password is not valid UTF-8";
  } else if (d->scrypt) {
    if (EVP_PBE_scrypt(pw, pw_len, salt, salt_len, d->n, d->r, d->p, (uint64_t)2 << 30, dk, 32) != 1) {
      d->error = "scrypt failed";
    }
  } else {
    if (PKCS5_PBKDF2_HMAC(pw, (int)pw_len, salt, (int)salt_len, (int)d->n, EVP_sha256(), 32, dk) != 1) {
      d->error = "pbkdf2 failed";
    }
  }
  if (d->error == NULL) {
    uint8_t pre[64];
    uint8_t sum[32];
    memcpy(pre, dk + 16, 16);
    memcpy(pre + 16, cipher, 32);
    SHA256(pre, 48, sum);
    if (CRYPTO_memcmp(sum, checksum, 32) != 0) {
      d->error = "keystore checksum does not match: wrong password";
    } else {
      EVP_CIPHER_CTX* ctx = EVP_CIPHER_CTX_new();
      int n1 = 0, n2 = 0;
      if (ctx == NULL
          || EVP_DecryptInit_ex(ctx, EVP_aes_128_ctr(), NULL, dk, iv) != 1
          || EVP_DecryptUpdate(ctx, secret, &n1, cipher, 32) != 1
          || EVP_DecryptFinal_ex(ctx, secret + n1, &n2) != 1
          || n1 + n2 != 32) {
        d->error = "aes-128-ctr failed";
      } else if (bk_add_key(secret, &d->index) != 0) {
        d->error = "keystore secret is not a valid BLS secret key";
      }
      EVP_CIPHER_CTX_free(ctx);
    }
    bk_wipe(pre, sizeof(pre));
  }
  bk_wipe(dk, sizeof(dk));
  bk_wipe(secret, sizeof(secret));
  if (pw != NULL) {
    bk_wipe(pw, pw_len);
    free(pw);
  }
  free(salt);
  free(cipher);
}

static Term keys_decrypt_pack(Env e, IoWork* w) {
  BkDecrypt* d = (BkDecrypt*)w->data;
  const char* error = d->error;
  uint32_t index = d->index;
  keys_decrypt_free(d);
  return error ? io_fail(e, EINVAL, error) : io_done(e, (Term)index);
}

Term keys_decrypt_run(Env e, Term* f, IoWork* w) {
  BkDecrypt* d = calloc(1, sizeof(BkDecrypt));
  if (d == NULL) {
    return io_fail(e, ENOMEM, NULL);
  }
  uint64_t kdf_n = 0;
  char* kdf = io_cstr(e, f[0], &kdf_n);
  d->dklen = (uint32_t)f[1];
  d->n = (uint32_t)f[2];
  d->r = (uint32_t)f[3];
  d->p = (uint32_t)f[4];
  d->salt = io_cstr(e, f[5], &d->salt_n);
  d->checksum = io_cstr(e, f[6], &d->checksum_n);
  d->cipher = io_cstr(e, f[7], &d->cipher_n);
  d->iv = io_cstr(e, f[8], &d->iv_n);
  d->password = io_cstr(e, f[9], &d->password_n);
  int is_scrypt = kdf_n == 6 && memcmp(kdf, "scrypt", 6) == 0;
  int is_pbkdf2 = kdf_n == 6 && memcmp(kdf, "pbkdf2", 6) == 0;
  free(kdf);
  if (!is_scrypt && !is_pbkdf2) {
    keys_decrypt_free(d);
    return io_fail(e, EINVAL, "unsupported keystore kdf: only scrypt and pbkdf2");
  }
  d->scrypt = is_scrypt;
  w->data = (char*)d;
  return io_work(w, keys_decrypt_call, keys_decrypt_pack);
}

static void __attribute__((constructor)) keys_decrypt_use(void) {
  io_eff(CID_KEYS_DECRYPT, keys_decrypt_run, 0);
}
