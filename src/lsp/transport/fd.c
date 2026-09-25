// stdio.fd: a File handle for a descriptor the process already has. An editor
// hands its server sockets or pipes as stdin and stdout, and a socket cannot
// be opened by path (/dev/stdin gives ENXIO), so the handles wrap 0 and 1.
Term stdio_fd_run(Env e, Term* f, IoWork* w) {
  return io_hand((intptr_t)(uint32_t)f[0]);
}

static void __attribute__((constructor)) stdio_fd_use(void) {
  io_eff(CID(stdio.fd), stdio_fd_run, 0);
}
