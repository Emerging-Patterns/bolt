# bolt from nothing: the binary people run, built by `bend` and nothing else.
#
# bolt has no hub dependency -- not one `import 0x` line anywhere -- so its
# whole closure is its own source and Base, and
# `bend bolt/main.bend -o bin/bolt.bin` is the entire build. `ez` is a
# convenience over that one line and never a prerequisite, in either direction:
# a project that depends on bolt needs no ez either. This holds that down as a
# build rather than as a comment -- the build below runs with BEND_LIB unset
# and nothing of ez in front of it -- because the day bolt grows a dependency
# on its own tooling is a day nobody would notice otherwise.
#
# The binary it leaves behind is the one the two checks after it need, and
# neither can be answered without it: the server has to be spawned by node,
# over sockets, to show it never opens a path for its own stdio, and the linter
# has to be the compiled binary that bolt.bend is written for.
#
# This is an end-to-end test, so `ez test` runs it on its own and never caches
# it. It is the slow one: the compile peaks near 8 GB, which is over `ez test`'s
# default cap, so this repo's gate wants EZ_CAP=16.
import Base
import ../run/run.bend as R
import ../core/check/kit.bend as Check
import ../core/check/print.bend as Report

# the build, with every variable ez would have set taken back out of the
# environment first. `env -u` is coreutils, execvp'd like any other program.
def bare() -> List<&2, String>:
  ["env", "-u", "BEND_LIB", "-u", "EZ_ROOT", "bend", "bolt/main.bend",
    "-o", "bin/bolt.bin"]

def main() -> IO(Unit):
  do IO<Unit>:
    _mk : String <- R.exec(["mkdir", "-p", "bin"])
    built : String <- R.exec(bare())
    Check.eq_str(~Report.new(), "bolt builds with bare bend and no BEND_LIB",
      R.code(built), "0")
    spawned : String <- R.exec(["node", "bolt/lsp/tests/spawn.js", "bin/bolt.bin"])
    Check.eq_str(~Report.new(), "the server answers node, spawned over sockets",
      R.text(spawned), "ok")
    linted : String <- R.exec(["bin/bolt.bin", "--gpu", "off"])
    Check.eq_str(~Report.new(), "bolt lints its own repo clean", R.text(linted), "clean")

#|ok bolt builds with bare bend and no BEND_LIB
#|ok the server answers node, spawned over sockets
#|ok bolt lints its own repo clean
