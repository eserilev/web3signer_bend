// Log.truncate_sync: cuts a file to size bytes, then calls fsync. At start,
// Bulkhead uses it to remove a partial last line of the slashing log, so
// the next append starts on a new line.

#include "bulkhead.h"

Term log_truncate_sync_run(Env e, Term* f, IoWork* w) {
  uint64_t n = 0;
  char* path = io_cstr(e, f[0], &n);
  if (io_nul(path, n)) {
    free(path);
    return io_fail(e, EINVAL, NULL);
  }
  int fd = open(path, O_WRONLY | O_CLOEXEC);
  free(path);
  if (fd < 0) {
    return io_fail(e, (u32)errno, NULL);
  }
  int code = 0;
  if (ftruncate(fd, (off_t)(uint32_t)f[1]) != 0 || fsync(fd) != 0) {
    code = errno;
  }
  close(fd);
  return code ? io_fail(e, (u32)code, NULL) : io_done(e, term_pak(CID_UNIT, 0));
}

static void __attribute__((constructor)) log_truncate_sync_use(void) {
  io_eff(CID_LOG_TRUNCATE_SYNC, log_truncate_sync_run, 0);
}
