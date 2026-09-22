# bolt from nothing: the binary people run, built by `bend` and nothing else.
#
# `bend bolt/main.bend -o bin/bolt.bin` is the entire build. shake,
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
import 0x29fbb19f01e963cc6271864b7e442159/main.bend as Snap
import ../core/check/kit.bend as Check
import ../core/check/print.bend as Report

# the 0x name ez computed for shake v0.1.1
def shake.hash() -> String:
  "0x65bf91e14c96bf0c25491d716ec9f68c"

# the 0x name ez computed for ezjson v0.1.0
def ezjson.hash() -> String:
  "0xa3c2445eb44c5d8406e6229be518fccb"

# the 0x name ez computed for snap v0.1.0
def snap.hash() -> String:
  "0x29fbb19f01e963cc6271864b7e442159"

# the build, with ez taken out of the environment. BEND_LIB is the
# checkouts this test laid out, not ez's.
def bare() -> List<&2, String>:
  ["env", "-u", "EZ_ROOT", "BEND_LIB=.scratch/lib", "bend", "bolt/main.bend",
    "-o", "bin/bolt.bin"]

def main() -> IO(Unit):
  do IO<Unit>:
    _wd : String <- Snap.exec(["rm", "-rf", ".scratch/shake", ".scratch/ezjson",
      ".scratch/snap", ".scratch/lib"])
    _cl : String <- Snap.exec(["git", "clone", "--depth", "1", "--branch", "v0.1.1",
      "https://github.com/Emerging-Patterns/shake.git", ".scratch/shake"])
    _cj : String <- Snap.exec(["git", "clone", "--depth", "1", "--branch", "v0.1.0",
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
      ".scratch/ezjson/ezjson/print.bend", ".scratch/ezjson/ezjson/value.bend",
      ".scratch/lib/" ++ ezjson.hash() ++ "/"])
    _cs2 : String <- Snap.exec(["cp",
      ".scratch/snap/snap/main.bend", ".scratch/snap/snap/exec.c",
      ".scratch/snap/snap/exec.js", ".scratch/snap/snap/start.c",
      ".scratch/snap/snap/start.js", ".scratch/snap/snap/par.c",
      ".scratch/snap/snap/par.js", ".scratch/lib/" ++ snap.hash() ++ "/"])
    _bin : String <- Snap.exec(["mkdir", "-p", "bin"])
    built : String <- Snap.exec(bare())
    Check.eq_str(~Report.new(), "bolt builds with bare bend and no ez",
      Snap.code(built), "0")
    spawned : String <- Snap.exec(["node", "bolt/lsp/tests/spawn.js", "bin/bolt.bin"])
    Check.eq_str(~Report.new(), "the server answers node, spawned over sockets",
      Snap.text(spawned), "ok\n")
    located : String <- Snap.exec(["node", "tests/locate.js", "bin/bolt.bin"])
    Check.eq_str(~Report.new(), "the extension finds bolt with no symlink to help it",
      Snap.text(located), "ok\n")
    linted : String <- Snap.exec(["bin/bolt.bin", "--gpu", "off"])
    Check.eq_str(~Report.new(), "bolt lints its own repo with no errors", Snap.code(linted), "0")
    helped : String <- Snap.exec(["bin/bolt.bin", "--gpu", "off", "help"])
    Check.eq_str(~Report.new(), "bolt help prints usage", Snap.code(helped), "0")
    many : String <- Snap.exec(["bin/bolt.bin", "--gpu", "off",
      "bolt/lsp/fixtures/proven/LAWS.bend",
      "bolt/lsp/fixtures/proven/PROOF.bend"])
    Check.eq_str(~Report.new(), "bolt lints the files it is given", Snap.text(many), "clean\n")
    checked : String <- Snap.exec(["bin/bolt.bin", "--gpu", "off", "check",
      "bolt/lsp/fixtures/proven/LAWS.bend",
      "bolt/lsp/fixtures/proven/PROOF.bend"])
    Check.eq_str(~Report.new(), "bolt check takes every leftover file", Snap.text(checked), "clean\n")

#|ok bolt builds with bare bend and no ez
#|ok the server answers node, spawned over sockets
#|ok the extension finds bolt with no symlink to help it
#|ok bolt lints its own repo with no errors
#|ok bolt help prints usage
#|ok bolt lints the files it is given
#|ok bolt check takes every leftover file
