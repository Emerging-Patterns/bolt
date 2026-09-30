# src/stop: a Stop done (Args.out's decision to print and exit): a text on
# its stream, then the exit code. Pure but for the IO it returns, and apart
# from main.bend, so its laws (the root LAWS.bend) reach no foreign code.
import Base
import ./args.bend as Args

# a text on its stream
def say(to: Args.Stream, text: String) -> IO(Unit):
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
def leave(+code: U32) -> IO(Unit):
  leave.at(U32.is_eq(code, 0), code)
