// Log.append_sync: appends text to a file, then calls fsync. The effect
// returns only after fsync returns, on a helper thread.

#include "bulkhead.h"

typedef struct {
  char* path;
  char* text;
  uint64_t text_n;
  int code;
} BkAppend;

static void log_append_sync_call(IoWork* w) {
  BkAppend* a = (BkAppend*)w->data;
  a->code = 0;
  int fd = open(a->path, O_WRONLY | O_APPEND | O_CREAT | O_CLOEXEC, 0600);
  if (fd < 0) {
    a->code = errno;
    return;
  }
  uint64_t done = 0;
  while (done < a->text_n) {
    ssize_t n = write(fd, a->text + done, a->text_n - done);
    if (n < 0) {
      if (errno == EINTR) {
        continue;
      }
      a->code = errno;
      close(fd);
      return;
    }
    done += (uint64_t)n;
  }
  if (fsync(fd) != 0) {
    a->code = errno;
  }
  if (close(fd) != 0 && a->code == 0) {
    a->code = errno;
  }
}

static Term log_append_sync_pack(Env e, IoWork* w) {
  BkAppend* a = (BkAppend*)w->data;
  int code = a->code;
  free(a->path);
  free(a->text);
  free(a);
  return code ? io_fail(e, (u32)code, NULL) : io_done(e, term_pak(CID_UNIT, 0));
}

Term log_append_sync_run(Env e, Term* f, IoWork* w) {
  BkAppend* a = calloc(1, sizeof(BkAppend));
  if (a == NULL) {
    return io_fail(e, ENOMEM, NULL);
  }
  uint64_t path_n = 0;
  a->path = io_cstr(e, f[0], &path_n);
  a->text = io_cstr(e, f[1], &a->text_n);
  if (io_nul(a->path, path_n)) {
    free(a->path);
    free(a->text);
    free(a);
    return io_fail(e, EINVAL, NULL);
  }
  w->data = (char*)a;
  return io_work(w, log_append_sync_call, log_append_sync_pack);
}

static void __attribute__((constructor)) log_append_sync_use(void) {
  io_eff(CID_LOG_APPEND_SYNC, log_append_sync_run, 0);
}
