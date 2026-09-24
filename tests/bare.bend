# bolt from nothing: the binary people run, built by `bend` and nothing else.
#
# `bend main.bend -o bin/bolt.bin` is the entire build. shake,
# ezjson and snap are git-backed ledger deps, so this test clones those
# pinned revs and lays them out as BEND_LIB itself -- no ez, no nix. `ez` is a
# convenience over that one line and never a prerequisite, in either
# direction: a project that depends on bolt needs no ez either.
#
# The binary it leaves behind is the one the three checks after it need, and
# none can be answered without it: the server has to be spawned by node, over
# sockets, to show it never opens a path for its own stdio; the linter has to
# be the compiled binary that bolt.bend is written for; and the VS Code
# extension's binary resolution is only worth anything if what it resolves to
# starts a server, so tests/locate.js ends by starting one on the path it
# resolved.
#
# This is an end-to-end test, so `ez test` runs it on its own and never caches
# it, and it is the slow one, because the compile it drives is a whole build of
# bolt.
import Base
import 0x9bfd9d57916f3439316c2775fd1f10b4/main.bend as Snap

# `ok name` when the two strings are equal, `FAIL name` when they are not
def eq_str(name: String, got: String, want: String) -> IO(Unit):
  IO.print(Bool.pick(String, String.eq(got, want), "ok ", "FAIL ") ++ name)

# the 0x name ez computed for shake v0.1.1
def shake.hash() -> String:
  "0xba6940aab8a335b70bf79944bd9b53c4"

# the 0x name ez computed for ezjson v0.4.2
def ezjson.hash() -> String:
  "0xd9c8d4d2899ddda845dfa7525a3568ea"

# the 0x name ez computed for snap v0.1.0
def snap.hash() -> String:
  "0x9bfd9d57916f3439316c2775fd1f10b4"

# the build, with ez taken out of the environment. BEND_LIB is the
# checkouts this test laid out, not ez's.
def bare() -> List<&2, String>:
  ["env", "-u", "EZ_ROOT", "BEND_LIB=.scratch/lib", "bend", "main.bend",
    "-o", "bin/bolt.bin"]

def main() -> IO(Unit):
  do IO<Unit>:
    _wd : String <- Snap.exec(["rm", "-rf", ".scratch/shake", ".scratch/ezjson",
      ".scratch/snap", ".scratch/lib"])
    _cl : String <- Snap.exec(["git", "clone", "--depth", "1", "--branch", "v0.1.1",
      "https://github.com/Emerging-Patterns/shake.git", ".scratch/shake"])
    _cj : String <- Snap.exec(["git", "clone", "--depth", "1", "--branch", "v0.4.2",
      "https://github.com/Emerging-Patterns/ezjson.git", ".scratch/ezjson"])
    _cs : String <- Snap.exec(["git", "clone", "--depth", "1", "--branch", "v0.1.0",
      "https://github.com/Emerging-Patterns/snap.git", ".scratch/snap"])
    _mk : String <- Snap.exec(["mkdir", "-p", ".scratch/lib/" ++ shake.hash(),
      ".scratch/lib/" ++ ezjson.hash(), ".scratch/lib/" ++ snap.hash()])
    _cp : String <- Snap.exec(["cp", ".scratch/shake/shake/main.bend",
      ".scratch/lib/" ++ shake.hash() ++ "/main.bend"])
    _cj2 : String <- Snap.exec(["cp",
      ".scratch/ezjson/ezjson/lazy.bend", ".scratch/ezjson/ezjson/lex.bend",
      ".scratch/ezjson/ezjson/main.bend", ".scratch/ezjson/ezjson/parse.bend",
      ".scratch/ezjson/ezjson/print.bend", ".scratch/ezjson/ezjson/pull.bend",
      ".scratch/ezjson/ezjson/value.bend",
      ".scratch/lib/" ++ ezjson.hash() ++ "/"])
    _cs2 : String <- Snap.exec(["cp",
      ".scratch/snap/snap/main.bend", ".scratch/snap/snap/exec.c",
      ".scratch/snap/snap/exec.js", ".scratch/snap/snap/start.c",
      ".scratch/snap/snap/start.js", ".scratch/snap/snap/par.c",
      ".scratch/snap/snap/par.js", ".scratch/lib/" ++ snap.hash() ++ "/"])
    _bin : String <- Snap.exec(["mkdir", "-p", "bin"])
    built : String <- Snap.exec(bare())
    eq_str("bolt builds with bare bend and no ez",
      Snap.code(built), "0")
    spawned : String <- Snap.exec(["node", "src/lsp/tests/spawn.js", "bin/bolt.bin"])
    eq_str("the server answers node, spawned over sockets",
      Snap.text(spawned), "ok\n")
    located : String <- Snap.exec(["node", "tests/locate.js", "bin/bolt.bin"])
    eq_str("the extension finds bolt with no symlink to help it",
      Snap.text(located), "ok\n")
    helped : String <- Snap.exec(["bin/bolt.bin", "--gpu", "off", "help"])
    eq_str("bolt help prints usage", Snap.code(helped), "0")
    many : String <- Snap.exec(["bin/bolt.bin", "--gpu", "off",
      "src/lsp/fixtures/proven/LAWS.bend",
      "src/lsp/fixtures/proven/PROOF.bend"])
    eq_str("bolt lints the files it is given", Snap.text(many), "clean\n")
    checked : String <- Snap.exec(["bin/bolt.bin", "--gpu", "off", "check",
      "src/lsp/fixtures/proven/LAWS.bend",
      "src/lsp/fixtures/proven/PROOF.bend"])
    eq_str("bolt check takes every leftover file", Snap.text(checked), "clean\n")

#|ok bolt builds with bare bend and no ez
#|ok the server answers node, spawned over sockets
#|ok the extension finds bolt with no symlink to help it
#|ok bolt help prints usage
#|ok bolt lints the files it is given
#|ok bolt check takes every leftover file
