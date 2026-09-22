# bolt: the one binary. Shake parses the line: `lint`, or a word that is no
# subcommand, or nothing, lints the files named after it (every `.bend` file
# under the current directory when none are); `check` runs the checker on
# them; `lsp` serves an editor over stdio; `help` prints usage; `--version`
# prints the release. Build it native (`bend bolt/main.bend -o
# bin/bolt.bin`). `bolt lsp` runs on the cores: with no `--gpu` it is
# `--gpu off`, and `--gpu on` or `--gpu 4GB` asks for the device. The
# runtime takes `--gpu` out of the line itself.
import Base
import 0x65bf91e14c96bf0c25491d716ec9f68c/main.bend as Shake
import ./args.bend as Args
import ./lint.bend as Lint
import ./check.bend as Check
import ./lsp/run.bend as Lsp

# a subcommand
type Cmd is Data:
  CLint{}
  CCheck{}
  CLsp{}

# a subcommand by its name; the empty name (no subcommand) is `lint`
def command(+name: String) -> Cmd:
  Bool.pick(Cmd, String.eq(name, "check"), CCheck{},
    Bool.pick(Cmd, String.eq(name, "lsp"), CLsp{}, CLint{}))

# what a subcommand runs, over the files after it
def dispatch(cmd: Cmd, paths: List<&2, String>) -> IO(Unit):
  match cmd:
    case CLint{}:
      Lint.run(paths)
    case CCheck{}:
      Check.run(paths)
    case CLsp{}:
      Lsp.run()

def run.at(ask: Bool, +mm: Shake.Matched) -> IO(Unit):
  match ask:
    case True{}:
      IO.print("bolt " ++ Args.version())
    case False{}:
      dispatch(command(String.join(Shake.path_of(mm), "/")), Shake.get_all(mm, "files"))

# a successful parse: the version, or the selected command and its files
def run(+mm: Shake.Matched) -> IO(Unit):
  run.at(Shake.on(mm, "version"), mm)

# a hard error
def fail.err(ee: Shake.ParseErr) -> IO(Unit):
  do IO<Unit>:
    IO.print_err(Args.err_text(ee))
    IO.die(Unit, 1, "")

# a failed parse: help text, or an error
def fail(ee: Shake.ParseErr) -> IO(Unit):
  match ee:
    case Shake.NeedHelp{path}:
      IO.write(Args.help_text(path))
    case other:
      fail.err(other)

# the parse result
def go(rr: Result<&2, &2, Shake.ParseErr, Shake.Matched>) -> IO(Unit):
  match rr:
    case Fail{e}:
      fail(e)
    case Done{m}:
      run(m)

def main() -> IO(Unit):
  do IO<Unit>:
    +av : List<&2, String> <- Args.argv()
    go(Args.parse(av))
