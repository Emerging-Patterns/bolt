// bendcheck.exec: the JS lane's twin of exec.c: `bend <path> --check-only`,
// which checks the file and its imports and never runs the program's main.
function bendcheck_exec(path) {
  const cp = require("child_process");
  const r = cp.spawnSync("bend", [path, "--check-only"], { encoding: "utf8", stdio: ["ignore", "pipe", "pipe"] });
  return (r.stdout ?? "") + (r.stderr ?? "");
}
