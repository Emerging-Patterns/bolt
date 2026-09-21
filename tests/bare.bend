# bolt from nothing: the binary people run, built by `bend` and nothing else.
#
# `bend bolt/main.bend -o bin/bolt.bin` is the entire build. bolt's one hub
# import is shake; bend fetches that package itself. `ez` is a convenience
# over that one line and never a prerequisite, in either direction: a project
# that depends on bolt needs no ez either. This holds that down as a build
# rather than as a comment -- the build below runs with BEND_LIB unset and
# nothing of ez in front of it -- because the day bolt grows a dependency on
# its own tooling is a day nobody would notice otherwise.
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

#|ok bolt builds with bare bend and no BEND_LIB
#|ok the server answers node, spawned over sockets
#|ok the extension finds bolt with no symlink to help it
#|ok bolt lints its own repo clean
#|ok bolt help prints usage
#|ok bolt lints the files it is given
#|ok bolt check takes every leftover file
