// bendcheck.exec: runs `bend <path> <flag>` and answers everything it
// printed. The flag is argv.bend's, always --check-only, which checks the
// file and its imports and never runs main: a language server must not
// execute the file being edited. The child
// gets /dev/null for stdin and a pipe for stdout and stderr, so it cannot
// touch the server's own stdio, which is the protocol.
#include <fcntl.h>
#include <stdlib.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>
#if defined(__APPLE__)
#include <crt_externs.h>
#include <mach-o/dyld.h>
#include <stdint.h>
#endif

Term bendcheck_exec_run(Env e, Term* f, IoWork* w) {
  uint64_t n = 0;
  char* path = io_cstr(e, f[0], &n);
  uint64_t fn = 0;
  char* flag = io_cstr(e, f[1], &fn);
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
      execlp("bend", "bend", path, flag, (char*)NULL);
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
  free(flag);
  Term s = io_str(e, buf, len);
  free(buf);
  return s;
}

static void __attribute__((constructor)) bendcheck_exec_use(void) {
  io_eff(CID_BENDCHECK_EXEC, bendcheck_exec_run, 0);
}

// `bolt lsp` with no `--gpu` is `--gpu off`. The runtime chooses the device
// in main and takes `--gpu` out of the line, so this runs first and starts
// the same binary with `--gpu off` in front. `--gpu on` or a size
// (`--gpu 4GB`) is left as written.
#if defined(__linux__) || defined(__APPLE__)
static int bolt_lsp_bare(int argc, char** argv) {
  int gpu = 0;
  const char* cmd = NULL;
  for (int i = 1; i < argc; i++) {
    const char* a = argv[i];
    if (strcmp(a, "--") == 0) {
      if (cmd == NULL && i + 1 < argc) {
        cmd = argv[i + 1];
      }
      break;
    }
    if (strcmp(a, "--help") == 0 || strcmp(a, "--gpu-build") == 0) {
      continue;
    }
    if (strcmp(a, "--threads") == 0 || strcmp(a, "--gpu") == 0) {
      if (strcmp(a, "--gpu") == 0) {
        gpu = 1;
      }
      if (i + 1 < argc) {
        i++;
      }
      continue;
    }
    if (cmd == NULL) {
      cmd = a;
    }
  }
  return cmd != NULL && strcmp(cmd, "lsp") == 0 && !gpu;
}

static void bolt_exec_gpu_off(const char* exe, int argc, char** argv) {
  char** next = malloc((size_t)(argc + 3) * sizeof(char*));
  if (next == NULL) {
    return;
  }
  next[0] = (char*)exe;
  next[1] = "--gpu";
  next[2] = "off";
  for (int i = 1; i < argc; i++) {
    next[i + 2] = argv[i];
  }
  next[argc + 2] = NULL;
  execv(exe, next);
  free(next);
}

static void bolt_lsp_cpu(void) {
#if defined(__linux__)
  int fd = open("/proc/self/cmdline", O_RDONLY);
  if (fd < 0) {
    return;
  }
  size_t cap = 4096;
  size_t len = 0;
  char* buf = malloc(cap);
  if (buf == NULL) {
    close(fd);
    return;
  }
  for (;;) {
    ssize_t n = read(fd, buf + len, cap - len);
    if (n < 0) {
      free(buf);
      close(fd);
      return;
    }
    if (n == 0) {
      break;
    }
    len += (size_t)n;
    if (len == cap) {
      cap *= 2;
      char* grown = realloc(buf, cap);
      if (grown == NULL) {
        free(buf);
        close(fd);
        return;
      }
      buf = grown;
    }
  }
  close(fd);
  if (len == 0 || buf[len - 1] != '\0') {
    free(buf);
    return;
  }
  int argc = 0;
  for (size_t i = 0; i < len; i++) {
    if (buf[i] == '\0') {
      argc++;
    }
  }
  char** argv = malloc((size_t)argc * sizeof(char*));
  if (argv == NULL) {
    free(buf);
    return;
  }
  int k = 0;
  argv[0] = buf;
  for (size_t i = 0; i < len && k < argc; i++) {
    if (buf[i] == '\0' && i + 1 < len) {
      argv[++k] = buf + i + 1;
    }
  }
  char exe[4096];
  ssize_t n = readlink("/proc/self/exe", exe, sizeof exe - 1);
  if (n > 0 && bolt_lsp_bare(argc, argv)) {
    exe[n] = '\0';
    bolt_exec_gpu_off(exe, argc, argv);
  }
  free(argv);
  free(buf);
#else
  int argc = *_NSGetArgc();
  char** argv = *_NSGetArgv();
  if (!bolt_lsp_bare(argc, argv)) {
    return;
  }
  char exe[4096];
  uint32_t sz = sizeof exe;
  if (_NSGetExecutablePath(exe, &sz) != 0) {
    return;
  }
  bolt_exec_gpu_off(exe, argc, argv);
#endif
}

static void __attribute__((constructor)) bolt_lsp_cpu_init(void) {
  bolt_lsp_cpu();
}
#endif
