// walkdir.cwd: the JS lane's twin of cwd.c: the working directory, from the
// root; one that cannot be named answers nothing.
function walkdir_cwd() {
  try {
    return process.cwd();
  } catch (e) {
    return "";
  }
}
