// Fs.sync_dir: calls fsync on a directory, so that a new file in it stays
// after a crash.

#include "bulkhead.h"

Term fs_sync_dir_run(Env e, Term* f, IoWork* w) {
  uint64_t n = 0;
  char* path = io_cstr(e, f[0], &n);
  if (io_nul(path, n)) {
    free(path);
    return io_fail(e, EINVAL, NULL);
  }
  int fd = open(path, O_RDONLY | O_DIRECTORY | O_CLOEXEC);
  free(path);
  if (fd < 0) {
    return io_fail(e, (u32)errno, NULL);
  }
  int code = fsync(fd) != 0 ? errno : 0;
  close(fd);
  return code ? io_fail(e, (u32)code, NULL) : io_done(e, term_pak(CID_UNIT, 0));
}

static void __attribute__((constructor)) fs_sync_dir_use(void) {
  io_eff(CID_FS_SYNC_DIR, fs_sync_dir_run, 0);
}
