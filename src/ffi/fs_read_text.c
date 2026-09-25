// Fs.read_text: the whole content of a file as text.

#include "bulkhead.h"

typedef struct {
  char* path;
  char* data;
  uint64_t size;
  int code;
} BkRead;

static void fs_read_text_call(IoWork* w) {
  BkRead* r = (BkRead*)w->data;
  r->code = 0;
  int fd = open(r->path, O_RDONLY | O_CLOEXEC);
  if (fd < 0) {
    r->code = errno;
    return;
  }
  uint64_t cap = 4096;
  r->data = malloc(cap);
  r->size = 0;
  for (;;) {
    if (r->data == NULL) {
      r->code = ENOMEM;
      break;
    }
    if (r->size == cap) {
      cap *= 2;
      char* grown = realloc(r->data, cap);
      if (grown == NULL) {
        r->code = ENOMEM;
        break;
      }
      r->data = grown;
    }
    ssize_t n = read(fd, r->data + r->size, cap - r->size);
    if (n < 0) {
      if (errno == EINTR) {
        continue;
      }
      r->code = errno;
      break;
    }
    if (n == 0) {
      break;
    }
    r->size += (uint64_t)n;
  }
  close(fd);
}

static Term fs_read_text_pack(Env e, IoWork* w) {
  BkRead* r = (BkRead*)w->data;
  Term out = r->code ? io_fail(e, (u32)r->code, NULL) : io_done(e, io_str(e, r->data, r->size));
  free(r->path);
  free(r->data);
  free(r);
  return out;
}

Term fs_read_text_run(Env e, Term* f, IoWork* w) {
  BkRead* r = calloc(1, sizeof(BkRead));
  if (r == NULL) {
    return io_fail(e, ENOMEM, NULL);
  }
  uint64_t n = 0;
  r->path = io_cstr(e, f[0], &n);
  if (io_nul(r->path, n)) {
    free(r->path);
    free(r);
    return io_fail(e, EINVAL, NULL);
  }
  w->data = (char*)r;
  return io_work(w, fs_read_text_call, fs_read_text_pack);
}

static void __attribute__((constructor)) fs_read_text_use(void) {
  io_eff(CID_FS_READ_TEXT, fs_read_text_run, 0);
}
