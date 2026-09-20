// The extension's binary resolution, driven without an editor. Usage:
// node tests/locate.js <bolt.bin> -- the binary tests/bare.bend has just
// built, which is the only real bolt this repo is sure of.
//
// editors/vscode/locate.js takes the setting, the environment, the home
// directory and the extension's own directory as arguments precisely so this
// can answer, for a made-up home and PATH, the questions a user would
// otherwise have to answer by installing things: does a bolt on the PATH get
// found with no symlink anywhere, does an explicit setting win, is a dangling
// ~/.local/bin/bolt skipped rather than handed to the editor, does a checkout
// with nothing installed still work, and is the failure legible. The last
// case takes the path resolution ended at and starts a real session on it.
const { spawnSync } = require("child_process");
const fs = require("fs");
const os = require("os");
const path = require("path");
const { locate } = require("../editors/vscode/locate.js");

const bolt = path.resolve(process.argv[2]);
const repo = path.resolve(__dirname, "..");
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "bolt-locate-"));
const fail = (why) => { console.error("FAIL: " + why); process.exit(1); };
const eq = (why, got, want) => { if (got !== want) fail(`${why}: ${got} is not ${want}`); };

// a directory holding a `bolt` that is the binary we were handed
const withBolt = (name) => {
  const dir = path.join(tmp, name);
  fs.mkdirSync(dir, { recursive: true });
  fs.symlinkSync(bolt, path.join(dir, "bolt"));
  return dir;
};
// the empty directory used as a home that has nothing installed in it
const bare = path.join(tmp, "bare-home");
fs.mkdirSync(bare, { recursive: true });
// a home with exactly the breakage this replaced: ~/.local/bin/bolt, made by
// hand, pointing at a file that is not there any more
const broken = path.join(tmp, "broken-home");
fs.mkdirSync(path.join(broken, ".local/bin"), { recursive: true });
fs.symlinkSync(path.join(repo, "bolt/bolt"), path.join(broken, ".local/bin/bolt"));
const threw = (f) => { try { f(); } catch (e) { return e.message; } return ""; };

// 1. the setting wins, over a PATH that has a bolt of its own
eq("the setting", locate({ setting: bolt, env: { PATH: withBolt("first") }, home: bare, dir: tmp }), bolt);

// 2. the setting's leading ~ is the home it was given
const home = withBolt("home-of");
eq("~ in the setting", locate({ setting: "~/bolt", env: { PATH: "" }, home, dir: tmp }),
  path.join(home, "bolt"));

// 3. a setting that names nothing says so, and says what to do
const bad = threw(() => locate({ setting: path.join(tmp, "nowhere/bolt"), env: { PATH: withBolt("second") }, home: bare, dir: tmp }));
if (!bad.includes("bend.server.path") || !bad.includes(path.join(tmp, "nowhere/bolt"))) {
  fail("a bad setting: " + bad);
}

// 4. `bolt` on the PATH, with no setting, no symlink of ours, and a dangling
//    ~/.local/bin/bolt in front of it that must be stepped over
const dir = withBolt("on-path");
const found = locate({ setting: "", env: { PATH: dir }, home: broken, dir: tmp });
eq("bolt on the PATH", found, path.join(dir, "bolt"));

// 5. a checkout with nothing installed: bin/bolt.bin, two levels above the
//    extension, is where `bend bolt/main.bend -o bin/bolt.bin` put it
eq("a checkout", locate({ setting: "", env: { PATH: bare }, home: bare, dir: path.join(repo, "editors/vscode") }),
  path.join(repo, "bin/bolt.bin"));

// 6. nothing anywhere: the message names every directory it looked in, and
//    the checkout binary it looked for, so the user can see which one to make
const none = threw(() => locate({ setting: "", env: { PATH: bare }, home: bare, dir: tmp }));
for (const want of [bare, path.join(bare, ".local/bin"), path.resolve(tmp, "../../bin/bolt.bin"), "bend.server.path"]) {
  if (!none.includes(want)) fail(`nothing found, missing ${want} from: ${none}`);
}

// 7. and what resolution ended at is a server: the path from case 4, spawned
//    by node over sockets, the way the extension host spawns it
const ran = spawnSync("node", [path.join(repo, "bolt/lsp/tests/spawn.js"), found], { encoding: "utf8" });
eq("a session on the resolved path", ran.stdout.trim(), "ok");

fs.rmSync(tmp, { recursive: true, force: true });
console.log("ok");
