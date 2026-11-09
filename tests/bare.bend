# bolt from nothing: the binary people run, built by `bend` and nothing else.
#
# `bend main.bend -o bin/bolt.bin` is the entire build. shake, ezjson and
# snap are imported by hub name (`shake@0.6.0.0/...`), so bend fetches them
# from the hub itself: this test runs it with an empty HOME and no BEND_LIB --
# no ez, no nix, no clones. `ez` is a convenience over that one line and never
# a prerequisite, in either direction: a project that depends on bolt needs no
# ez either.
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
import snap@1.4.0.0/main.bend as Snap

# `ok name` when the two strings are equal, `FAIL name` when they are not
def eq_str(name: String, got: String, want: String) -> IO(Unit):
  IO.print(Bool.pick(String, String.eq(got, want), "ok ", "FAIL ") ++ name)

# the build, with ez taken out of the environment: no BEND_LIB, and a HOME
# with nothing in it, so every named import comes from the hub
def bare() -> List<&2, String>:
  ["env", "-u", "EZ_ROOT", "-u", "BEND_LIB", "HOME=.scratch/home", "bend",
    "main.bend", "-o", "bin/bolt.bin"]

def main() -> IO(Unit):
  do IO<Unit>:
    _wd : String <- Snap.exec(["rm", "-rf", ".scratch/home"])
    _hm : String <- Snap.exec(["mkdir", "-p", ".scratch/home"])
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
    helped : String <- Snap.exec(["bin/bolt.bin", "+RTS", "--gpu", "off", "-RTS", "help"])
    eq_str("bolt help prints usage", Snap.code(helped), "0")
    many : String <- Snap.exec(["bin/bolt.bin", "+RTS", "--gpu", "off", "-RTS",
      "src/lsp/fixtures/proven/LAWS.bend",
      "src/lsp/fixtures/proven/PROOF.bend"])
    eq_str("bolt lints the files it is given", Snap.text(many), "clean\n")
    checked : String <- Snap.exec(["bin/bolt.bin", "+RTS", "--gpu", "off", "-RTS", "check",
      "src/lsp/fixtures/proven/LAWS.bend",
      "src/lsp/fixtures/proven/PROOF.bend"])
    eq_str("bolt check takes every leftover file", Snap.text(checked), "clean\n")

#|ok bolt builds with bare bend and no ez
#|ok the server answers node, spawned over sockets
#|ok the extension finds bolt with no symlink to help it
#|ok bolt help prints usage
#|ok bolt lints the files it is given
#|ok bolt check takes every leftover file
