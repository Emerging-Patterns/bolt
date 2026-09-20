# bolt: the one binary. Its first argument picks what runs: `lint`, or a word
# that is no subcommand, or nothing, lints the files named after it (every
# `.bend` file under the current directory when none are); `check` runs the
# checker on them; `lsp` serves an editor over stdio. Build it native (`bend
# bolt/main.bend -o bin/bolt.bin`), and run the server on the cores
# (`bolt lsp --gpu off`): the runtime takes `--gpu` out of the line itself.
import Base
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

def main() -> IO(Unit):
  do IO<Unit>:
    +av : List<&2, String> <- Args.argv()
    dispatch(command(Args.command(av)), Args.files(av))
