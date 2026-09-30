# bolt: a linter, checker and language server for Bend 2.
#
# The one binary. Shake parses the line: `lint`, or a word that is no
# subcommand, or nothing, lints the files named after it (every `.bend` file
# under the current directory when none are); `check` runs the checker on
# them; `lsp` serves an editor over stdio; `help` prints usage; `--version`
# prints the release and the short commit when the build has one. Build it
# native (`bend main.bend -o bin/bolt.bin`). `bolt lsp` runs on the cores:
# with no `--gpu` it is `--gpu off`, and `--gpu on` or `--gpu 4GB` asks for
# the device. The runtime takes `--gpu` out of the line itself. What the line
# does is Args.out's decision (src/LAWS.bend proves it); this file only does
# it, and LAWS.bend states what src/stop.bend's say and leave do.
# Everything under src/ is internal.
import Base
import ./src/args.bend as Args
import ./src/lint.bend as Lint
import ./src/check.bend as Check
import ./src/lsp/run.bend as Lsp
import ./src/lsp/checker/bend.bend as BendChecker
import ./src/stop.bend as Stop

# what a subcommand runs, over the files after it
def dispatch(cmd: Args.Cmd, paths: List<&2, String>) -> IO(Unit):  # noqa: L001 IO driver
  match cmd:
    case Args.CLint{}:
      Lint.run(paths)
    case Args.CCheck{}:
      Check.run(~BendChecker.service(), paths)
    case Args.CLsp{}:
      Lsp.run()

# what a parsed line does, done
def perform(oo: Args.Out) -> IO(Unit):  # noqa: L001 IO driver
  match oo:
    case Args.Stop{to, text, code}:
      do IO<Unit>:
        Stop.say(to, text)
        Stop.leave(code)
    case Args.Go{cmd, paths}:
      dispatch(cmd, paths)

def main() -> IO(Unit):  # noqa: L001 IO entry point
  do IO<Unit>:
    +av : List<&2, String> <- Args.argv()
    perform(Args.out(Args.parse(av)))
