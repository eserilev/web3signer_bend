// An LD_PRELOAD shim for tests/run_crash.py: power loss for the slashing log.
//
// Writes to the file named by BULKHEAD_SHIM_LOG stay in memory until fsync.
// fsync writes them to the file, then syncs. close without fsync drops them.
// So SIGKILL loses every write that no fsync covered, as a power loss does,
// and the crash test covers the fsync-before-reply rule (law L6), not only
// the write-before-reply order.
//
// BULKHEAD_SHIM_FSYNC_US adds a delay to each fsync, to make the time
// between a write and its fsync longer.
//
// Build: cc -shared -fPIC -O2 -o crash_shim.so crash_shim.c -ldl -lpthread
#define _GNU_SOURCE
#include <dlfcn.h>
#include <fcntl.h>
#include <pthread.h>
#include <stdarg.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <unistd.h>

#define MAX_FD 4096

static pthread_mutex_t lock = PTHREAD_MUTEX_INITIALIZER;
static char *buf[MAX_FD];
static size_t len[MAX_FD];
static int tracked[MAX_FD];

static int (*real_open)(const char *, int, ...);
static int (*real_open64)(const char *, int, ...);
static ssize_t (*real_write)(int, const void *, size_t);
static int (*real_fsync)(int);
static int (*real_close)(int);

static void init(void) {
  if (!real_write) {
    real_open = dlsym(RTLD_NEXT, "open");
    real_open64 = dlsym(RTLD_NEXT, "open64");
    real_write = dlsym(RTLD_NEXT, "write");
    real_fsync = dlsym(RTLD_NEXT, "fsync");
    real_close = dlsym(RTLD_NEXT, "close");
  }
}

static void track(const char *path, int fd) {
  const char *log = getenv("BULKHEAD_SHIM_LOG");
  if (fd >= 0 && fd < MAX_FD && log && strcmp(path, log) == 0) {
    pthread_mutex_lock(&lock);
    tracked[fd] = 1;
    len[fd] = 0;
    pthread_mutex_unlock(&lock);
  }
}

static int do_open(int (*f)(const char *, int, ...), const char *path, int flags, va_list ap) {
  mode_t mode = (flags & O_CREAT) ? va_arg(ap, mode_t) : 0;
  int fd = f(path, flags, mode);
  track(path, fd);
  return fd;
}

int open(const char *path, int flags, ...) {
  init();
  va_list ap;
  va_start(ap, flags);
  int fd = do_open(real_open, path, flags, ap);
  va_end(ap);
  return fd;
}

int open64(const char *path, int flags, ...) {
  init();
  va_list ap;
  va_start(ap, flags);
  int fd = do_open(real_open64 ? real_open64 : real_open, path, flags, ap);
  va_end(ap);
  return fd;
}

ssize_t write(int fd, const void *data, size_t n) {
  init();
  if (fd < 0 || fd >= MAX_FD || !tracked[fd]) return real_write(fd, data, n);
  pthread_mutex_lock(&lock);
  char *grown = realloc(buf[fd], len[fd] + n);
  if (!grown) {
    pthread_mutex_unlock(&lock);
    return -1;
  }
  buf[fd] = grown;
  memcpy(buf[fd] + len[fd], data, n);
  len[fd] += n;
  pthread_mutex_unlock(&lock);
  return (ssize_t)n;
}

int fsync(int fd) {
  init();
  if (fd < 0 || fd >= MAX_FD || !tracked[fd]) return real_fsync(fd);
  const char *delay = getenv("BULKHEAD_SHIM_FSYNC_US");
  if (delay) usleep((useconds_t)atoi(delay));
  pthread_mutex_lock(&lock);
  size_t done = 0;
  while (done < len[fd]) {
    ssize_t w = real_write(fd, buf[fd] + done, len[fd] - done);
    if (w <= 0) {
      pthread_mutex_unlock(&lock);
      return -1;
    }
    done += (size_t)w;
  }
  len[fd] = 0;
  pthread_mutex_unlock(&lock);
  return real_fsync(fd);
}

int close(int fd) {
  init();
  if (fd >= 0 && fd < MAX_FD && tracked[fd]) {
    pthread_mutex_lock(&lock);
    tracked[fd] = 0;
    len[fd] = 0;
    pthread_mutex_unlock(&lock);
  }
  return real_close(fd);
}
