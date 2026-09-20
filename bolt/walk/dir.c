// walkdir.entries: the names directly in a directory, one a line, a
// directory's name ending in "/". A directory that cannot be opened answers
// nothing, as `find` skips what it cannot read. Symbolic links are named as
// files even when they point at a directory, so a link cannot make the walk
// loop.
#include <dirent.h>
#include <string.h>
#include <sys/stat.h>

// whether the entry at name, under dir, is a directory (d_type may be
// DT_UNKNOWN on some file systems: ask the file system itself then)
static int walkdir_is_dir(const char* dir, struct dirent* ent) {
  if (ent->d_type == DT_DIR) {
    return 1;
  }
  if (ent->d_type != DT_UNKNOWN) {
    return 0;
  }
  char full[4096];
  snprintf(full, sizeof(full), "%s/%s", dir, ent->d_name);
  struct stat st;
  if (lstat(full, &st) != 0) {
    return 0;
  }
  return S_ISDIR(st.st_mode);
}

Term walkdir_entries_run(Env e, Term* f, IoWork* w) {
  uint64_t n = 0;
  char* dir = io_cstr(e, f[0], &n);
  size_t len = 0;
  size_t cap = 4096;
  char* buf = malloc(cap);
  DIR* d = opendir(dir);
  if (d) {
    struct dirent* ent;
    while ((ent = readdir(d)) != NULL) {
      if (!strcmp(ent->d_name, ".") || !strcmp(ent->d_name, "..")) {
        continue;
      }
      size_t l = strlen(ent->d_name);
      while (len + l + 2 > cap) {
        cap *= 2;
        buf = realloc(buf, cap);
      }
      memcpy(buf + len, ent->d_name, l);
      len += l;
      if (walkdir_is_dir(dir, ent)) {
        buf[len++] = '/';
      }
      buf[len++] = '\n';
    }
    closedir(d);
  }
  free(dir);
  Term s = io_str(e, buf, len);
  free(buf);
  return s;
}

static void __attribute__((constructor)) walkdir_entries_use(void) {
  io_eff(CID_WALKDIR_ENTRIES, walkdir_entries_run, 0);
}
