// Where bolt is. Nothing here imports `vscode` -- the setting, the
// environment, the home directory and the extension's own directory all
// arrive as arguments -- so `tests/locate.js` drives the same code the
// extension host runs, with no editor in the room (tests/extension.bend).
//
// The order is: the setting the user set, then `bolt` on the PATH, then the
// binary of a checkout the extension is being run from. A `nix profile
// install` lands in ~/.nix-profile/bin and is found by the second; a
// `bend bolt/main.bend -o bin/bolt.bin` with nothing installed is found by
// the third. Neither needs a symlink, and there used to be one:
// ~/.local/bin/bolt, hand-made, ahead of everything, and dangling on this
// machine for long enough that the extension was documented against a path
// that did not exist.
const fs = require("fs");
const os = require("os");
const path = require("path");

// the setting names the file, so a leading ~ is the user's own shorthand for
// their home directory, not a directory called "~"
function expand(p, home) {
  return path.resolve(p.replace(/^~(?=$|\/)/, home));
}

// The server runs `bend`, and bend's launcher runs `bun`: an extension host
// started from a desktop or over SSH often lacks the shell's PATH. These are
// where the three ways of installing put things, and they go in front, so the
// same list answers both "what does the server inherit" and "where is bolt".
function searchPath(env, home) {
  const extra = [".local/bin", ".bend/bin", ".bun/bin", ".nix-profile/bin"].map((d) => path.join(home, d));
  return [...extra, ...(env.PATH ?? "").split(path.delimiter).filter((d) => d !== "")];
}

// the PATH the server is started with, which is the search path again: a bolt
// found in one of these directories has `bend` in the next one along
function serverEnv(env, home) {
  return { ...env, PATH: searchPath(env, home).join(path.delimiter) };
}

// a file that exists and that this user may execute. A directory named `bolt`
// is not it, and neither is a dangling symlink: statSync follows the link, so
// a broken one throws here and is skipped like anything else missing.
function runnable(p) {
  try {
    if (!fs.statSync(p).isFile()) {
      return false;
    }
    fs.accessSync(p, fs.constants.X_OK);
    return true;
  } catch {
    return false;
  }
}

// the first runnable `bolt` on the search path
function onPath(env, home) {
  return searchPath(env, home).map((d) => path.join(d, "bolt")).find(runnable);
}

// the binary a checkout builds, when the extension is being run out of one
// (editors/vscode/ is two levels under the repo root). An installed VSIX sits
// in ~/.vscode/extensions and has no such file above it.
function inCheckout(dir) {
  const bin = path.resolve(dir, "..", "..", "bin", "bolt.bin");
  return runnable(bin) ? bin : undefined;
}

// bolt, or a message naming every place this looked. `setting` is
// `bend.server.path`, empty when the user set nothing.
function locate({ setting, env = process.env, home = os.homedir(), dir = __dirname }) {
  if (setting) {
    const set = expand(setting, home);
    if (runnable(set)) {
      return set;
    }
    throw new Error(`bend.server.path is set to ${set}, which is not a program this user can run. `
      + "Point it at bolt, or clear it to search the PATH.");
  }
  const found = onPath(env, home) ?? inCheckout(dir);
  if (found) {
    return found;
  }
  throw new Error("bolt was not found. Looked for `bolt` in "
    + searchPath(env, home).join(", ") + ", and for "
    + path.resolve(dir, "..", "..", "bin", "bolt.bin")
    + ". Install it (nix profile install github:Emerging-Patterns/bolt, or "
    + "bend bolt/main.bend -o bin/bolt.bin in a checkout), or set bend.server.path.");
}

module.exports = { locate, serverEnv, searchPath, expand, runnable };
