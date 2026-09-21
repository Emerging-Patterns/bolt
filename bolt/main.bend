# bolt: the one binary. Shake parses the line: `lint`, or a word that is no
# subcommand, or nothing, lints the files named after it (every `.bend` file
# under the current directory when none are); `check` runs the checker on
# them; `lsp` serves an editor over stdio; `help` prints usage. Build it
# native (`bend bolt/main.bend -o bin/bolt.bin`), and run the server on the
# cores (`bolt lsp --gpu off`): the runtime takes `--gpu` out of the line
# itself.
import Base
import 0xba6940aab8a335b70bf79944bd9b53c4/main.bend as Shake
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

# a successful parse: the selected command and its files
def run(+m: Shake.Matched) -> IO(Unit):
  dispatch(command(String.join(Shake.path_of(m), "/")), Shake.get_all(m, "files"))

# a hard error
def fail.err(e: Shake.ParseErr) -> IO(Unit):
  do IO<Unit>:
    IO.print_err(Args.err_text(e))
    IO.die(Unit, 1, "")

# a failed parse: help text, or an error
def fail(e: Shake.ParseErr) -> IO(Unit):
  match e:
    case Shake.NeedHelp{path}:
      IO.write(Args.help_text(path))
    case other:
      fail.err(other)

# the parse result
def go(r: Result<&2, &2, Shake.ParseErr, Shake.Matched>) -> IO(Unit):
  match r:
    case Fail{e}:
      fail(e)
    case Done{m}:
      run(m)

def main() -> IO(Unit):
  do IO<Unit>:
    +av : List<&2, String> <- Args.argv()
    go(Args.parse(av))
