# say: an effect (CPU event loop only): where a text goes, and how a code
# exits. The streams and the exit are Base IO. main.bend performs what
# Args.out decided; the laws of these defs are LAWS.bend.
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

# exit with a code once it is known to be 0 or not: 0 falls through
def leave.at(zero: Bool, code: U32) -> IO(Unit):
  match zero:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      IO.die(Unit, code, "")

# exit with a code: 0 falls through, any other ends the run with it
def leave(+code: U32) -> IO(Unit):
  leave.at(U32.is_eq(code, 0), code)
