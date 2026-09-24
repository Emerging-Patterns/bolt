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
# does is Args.out's decision (LAWS.bend proves it); this file only does it.
# Everything under src/ is internal.
import Base
import ./src/args.bend as Args
import ./src/lint.bend as Lint
import ./src/check.bend as Check
import ./src/lsp/run.bend as Lsp

# what a subcommand runs, over the files after it
def dispatch(cmd: Args.Cmd, paths: List<&2, String>) -> IO(Unit):  # noqa: L001 IO driver
  match cmd:
    case Args.CLint{}:
      Lint.run(paths)
    case Args.CCheck{}:
      Check.run(paths)
    case Args.CLsp{}:
      Lsp.run()

# a text on its stream
def say(to: Args.Stream, text: String) -> IO(Unit):  # noqa: L001 IO driver
  match to:
    case Args.Line{}:
      IO.print(text)
    case Args.Page{}:
      IO.write(text)
    case Args.Err{}:
      IO.print_err(text)

def leave.at(zero: Bool, code: U32) -> IO(Unit):
  match zero:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      IO.die(Unit, code, "")

# exit with a code: 0 falls through, any other ends the run with it
def leave(+code: U32) -> IO(Unit):  # noqa: L001 IO driver
  leave.at(U32.is_eq(code, 0), code)

# what a parsed line does, done
def perform(oo: Args.Out) -> IO(Unit):  # noqa: L001 IO driver
  match oo:
    case Args.Stop{to, text, code}:
      do IO<Unit>:
        say(to, text)
        leave(code)
    case Args.Go{cmd, paths}:
      dispatch(cmd, paths)

def main() -> IO(Unit):  # noqa: L001 IO entry point
  do IO<Unit>:
    +av : List<&2, String> <- Args.argv()
    perform(Args.out(Args.parse(av)))
