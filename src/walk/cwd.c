// walkdir.cwd: the working directory, from the root. A working directory that
// cannot be named (removed since the process entered it) answers nothing.
#include <limits.h>
#include <string.h>
#include <unistd.h>

Term walkdir_cwd_run(Env e, Term* f, IoWork* w) {
  char buf[PATH_MAX];
  if (getcwd(buf, sizeof(buf)) == NULL) {
    return io_str(e, "", 0);
  }
  return io_str(e, buf, strlen(buf));
}

static void __attribute__((constructor)) walkdir_cwd_use(void) {
  io_eff(CID(walkdir.cwd), walkdir_cwd_run, 0);
}
