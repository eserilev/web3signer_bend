// Fs.list: the names in a directory, sorted, one per line. Hidden names and
// the . and .. entries are left out.

#include "bulkhead.h"

static int fs_list_cmp(const void* a, const void* b) {
  return strcmp(*(char* const*)a, *(char* const*)b);
}

Term fs_list_run(Env e, Term* f, IoWork* w) {
  uint64_t n = 0;
  char* path = io_cstr(e, f[0], &n);
  if (io_nul(path, n)) {
    free(path);
    return io_fail(e, EINVAL, NULL);
  }
  DIR* dir = opendir(path);
  free(path);
  if (dir == NULL) {
    return io_fail(e, (u32)errno, NULL);
  }
  char** names = NULL;
  size_t count = 0, cap = 0, total = 0;
  struct dirent* ent;
  while ((ent = readdir(dir)) != NULL) {
    if (ent->d_name[0] == '.') {
      continue;
    }
    if (count == cap) {
      cap = cap ? cap * 2 : 32;
      char** grown = realloc(names, sizeof(char*) * cap);
      if (grown == NULL) {
        break;
      }
      names = grown;
    }
    names[count] = strdup(ent->d_name);
    total += strlen(ent->d_name) + 1;
    count += 1;
  }
  closedir(dir);
  qsort(names, count, sizeof(char*), fs_list_cmp);
  char* out = malloc(total + 1);
  size_t at = 0;
  for (size_t i = 0; i < count; i++) {
    size_t len = strlen(names[i]);
    memcpy(out + at, names[i], len);
    at += len;
    out[at++] = '\n';
    free(names[i]);
  }
  free(names);
  Term r = io_done(e, io_str(e, out, at));
  free(out);
  return r;
}

static void __attribute__((constructor)) fs_list_use(void) {
  io_eff(CID_FS_LIST, fs_list_run, 0);
}
