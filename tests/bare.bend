# bolt from nothing: the binary people run, built by `bend` and nothing else.
#
# `bend bolt/main.bend -o bin/bolt.bin` is the entire build. shake and
# ezjson are git-backed ledger deps, so this test clones those pinned revs
# and lays them out as BEND_LIB itself -- no ez, no nix. `ez` is a
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
import ../run/run.bend as R
import ../core/check/kit.bend as Check
import ../core/check/print.bend as Report

# the 0x name ez computed for shake v0.1.1
def shake.hash() -> String:
  "0x65bf91e14c96bf0c25491d716ec9f68c"

# the 0x name ez computed for ezjson v0.1.0
def ezjson.hash() -> String:
  "0xa3c2445eb44c5d8406e6229be518fccb"

# the build, with ez taken out of the environment. BEND_LIB is the
# checkouts this test laid out, not ez's.
def bare() -> List<&2, String>:
  ["env", "-u", "EZ_ROOT", "BEND_LIB=.scratch/lib", "bend", "bolt/main.bend",
    "-o", "bin/bolt.bin"]

def main() -> IO(Unit):
  do IO<Unit>:
    _wd : String <- R.exec(["rm", "-rf", ".scratch/shake", ".scratch/ezjson",
      ".scratch/lib"])
    _cl : String <- R.exec(["git", "clone", "--depth", "1", "--branch", "v0.1.1",
      "https://github.com/Emerging-Patterns/shake.git", ".scratch/shake"])
    _cj : String <- R.exec(["git", "clone", "--depth", "1", "--branch", "v0.1.0",
      "https://github.com/Emerging-Patterns/ezjson.git", ".scratch/ezjson"])
    _mk : String <- R.exec(["mkdir", "-p", ".scratch/lib/" ++ shake.hash(),
      ".scratch/lib/" ++ ezjson.hash()])
    _cp : String <- R.exec(["cp", ".scratch/shake/shake/main.bend",
      ".scratch/lib/" ++ shake.hash() ++ "/main.bend"])
    _cj2 : String <- R.exec(["cp",
      ".scratch/ezjson/ezjson/lazy.bend", ".scratch/ezjson/ezjson/lex.bend",
      ".scratch/ezjson/ezjson/main.bend", ".scratch/ezjson/ezjson/parse.bend",
      ".scratch/ezjson/ezjson/print.bend", ".scratch/ezjson/ezjson/value.bend",
      ".scratch/lib/" ++ ezjson.hash() ++ "/"])
    _bin : String <- R.exec(["mkdir", "-p", "bin"])
    built : String <- R.exec(bare())
    Check.eq_str(~Report.new(), "bolt builds with bare bend and no ez",
      R.code(built), "0")
    spawned : String <- R.exec(["node", "bolt/lsp/tests/spawn.js", "bin/bolt.bin"])
    Check.eq_str(~Report.new(), "the server answers node, spawned over sockets",
      R.text(spawned), "ok")
    located : String <- R.exec(["node", "tests/locate.js", "bin/bolt.bin"])
    Check.eq_str(~Report.new(), "the extension finds bolt with no symlink to help it",
      R.text(located), "ok")
    linted : String <- R.exec(["bin/bolt.bin", "--gpu", "off"])
    Check.eq_str(~Report.new(), "bolt lints its own repo clean", R.text(linted), "clean")
    helped : String <- R.exec(["bin/bolt.bin", "--gpu", "off", "help"])
    Check.eq_str(~Report.new(), "bolt help prints usage", R.code(helped), "0")
    many : String <- R.exec(["bin/bolt.bin", "--gpu", "off",
      "bolt/lsp/fixtures/proven/LAWS.bend",
      "bolt/lsp/fixtures/proven/PROOF.bend"])
    Check.eq_str(~Report.new(), "bolt lints the files it is given", R.text(many), "clean")
    checked : String <- R.exec(["bin/bolt.bin", "--gpu", "off", "check",
      "bolt/lsp/fixtures/proven/LAWS.bend",
      "bolt/lsp/fixtures/proven/PROOF.bend"])
    Check.eq_str(~Report.new(), "bolt check takes every leftover file", R.text(checked), "clean")

#|ok bolt builds with bare bend and no ez
#|ok the server answers node, spawned over sockets
#|ok the extension finds bolt with no symlink to help it
#|ok bolt lints its own repo clean
#|ok bolt help prints usage
#|ok bolt lints the files it is given
#|ok bolt check takes every leftover file
