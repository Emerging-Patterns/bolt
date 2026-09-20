// bendcheck.exec: runs `bend <path> --check-only` and answers everything it
// printed. --check-only checks the file and its imports and never runs
// main: a language server must not execute the file being edited. The child
// gets /dev/null for stdin and a pipe for stdout and stderr, so it cannot
// touch the server's own stdio, which is the protocol.
#include <fcntl.h>
#include <sys/wait.h>
#include <unistd.h>

Term bendcheck_exec_run(Env e, Term* f, IoWork* w) {
  uint64_t n = 0;
  char* path = io_cstr(e, f[0], &n);
  size_t len = 0;
  size_t cap = 4096;
  char* buf = malloc(cap);
  int fds[2];
  if (pipe(fds) == 0) {
    pid_t pid = fork();
    if (pid == 0) {
      int nul = open("/dev/null", O_RDONLY);
      dup2(nul, 0);
      dup2(fds[1], 1);
      dup2(fds[1], 2);
      close(fds[0]);
      close(fds[1]);
      execlp("bend", "bend", path, "--check-only", (char*)NULL);
      _exit(127);
    }
    close(fds[1]);
    ssize_t got;
    while ((got = read(fds[0], buf + len, cap - len)) > 0) {
      len += (size_t)got;
      if (len == cap) {
        cap *= 2;
        buf = realloc(buf, cap);
      }
    }
    close(fds[0]);
    if (pid > 0) {
      int status = 0;
      waitpid(pid, &status, 0);
    }
  }
  free(path);
  Term s = io_str(e, buf, len);
  free(buf);
  return s;
}

static void __attribute__((constructor)) bendcheck_exec_use(void) {
  io_eff(CID_BENDCHECK_EXEC, bendcheck_exec_run, 0);
}
