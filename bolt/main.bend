# bolt: the one binary behind the `bolt` script. BOLT_CMD picks what runs:
# `lint` (or nothing) lints the files in BOLT_FILES, `check` runs the checker
# on them, `lsp` serves an editor over stdio. Build it native (`bend
# bolt/main.bend -o bin/bolt.bin`).
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
  CUnknown{name: String}

# a subcommand by its name
def command(+name: String) -> Cmd:
  Bool.pick(Cmd, Bool.or(String.eq(name, "lint"), String.is_empty(name)), CLint{},
    Bool.pick(Cmd, String.eq(name, "check"), CCheck{},
      Bool.pick(Cmd, String.eq(name, "lsp"), CLsp{}, CUnknown{name})))

# what a subcommand runs
def dispatch(cmd: Cmd) -> IO(Unit):
  match cmd:
    case CLint{}:
      Lint.run()
    case CCheck{}:
      Check.run()
    case CLsp{}:
      Lsp.run()
    case CUnknown{name}:
      IO.print("bolt: no such command: " ++ name)

def main() -> IO(Unit):
  do IO<Unit>:
    name : String <- Args.command()
    dispatch(command(name))
