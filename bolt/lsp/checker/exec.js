// bendcheck.exec: the JS lane's twin of exec.c: `bend <path> <flag>`, the
// flag argv.bend's --check-only, which checks the file and its imports and
// never runs the program's main.
function bendcheck_exec(path, flag) {
  const cp = require("child_process");
  const r = cp.spawnSync("bend", [path, flag], { encoding: "utf8", stdio: ["ignore", "pipe", "pipe"] });
  return (r.stdout ?? "") + (r.stderr ?? "");
}
