// bendcheck.exec: the JS lane's twin of exec.c: `bend <path> <flag>`, the
// flag argv.bend's --check-only, which checks the file and its imports and
// never runs the program's main.
function bendcheck_exec(path, flag) {
  const cp = require("child_process");
  const r = cp.spawnSync("bend", [path, flag], { encoding: "utf8", stdio: ["ignore", "pipe", "pipe"] });
  // the tag first (bend.bend's bendcheck.exec): "x" when it could not be
  // spawned or exited 127, "s" when a signal killed it, else "r"
  const tag = r.status === 127 || (r.error && r.status === null && r.signal === null) ? "x" : r.signal ? "s" : "r";
  return tag + (r.stdout ?? "") + (r.stderr ?? "");
}
