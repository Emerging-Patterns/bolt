// bendcheck.exec: the JS lane's twin of exec.c: `bend <path> -o <tmp>.js`,
// which checks and emits but never runs the program's main.
function bendcheck_exec(path) {
  const cp = require("child_process");
  const fs = require("fs");
  const os = require("os");
  const tmp = require("path").join(os.tmpdir(), "bend-lsp-" + process.pid + "-" + Date.now() + ".js");
  const r = cp.spawnSync("bend", [path, "-o", tmp], { encoding: "utf8", stdio: ["ignore", "pipe", "pipe"] });
  fs.rmSync(tmp, { force: true });
  return (r.stdout ?? "") + (r.stderr ?? "");
}
