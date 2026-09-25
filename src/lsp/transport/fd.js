// stdio.fd: the JS lane's twin of fd.c: a File handle there is the descriptor.
function stdio_fd(n) {
  return n;
}

io_eff(CID(stdio.fd), stdio_fd);
