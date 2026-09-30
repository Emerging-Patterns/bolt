# bolt: the laws of what main.bend does with a Stop. main.bend only does what
# Args.out decides (src/LAWS.bend states that decision for every argv). A text
# goes to its stream, and a code exits as it says: src/stop.bend's say and
# leave, which main.bend calls. dispatch, perform and main have no law here:
# each reaches the linter's, checker's or server's foreign IO, and a proof
# that loads foreign code, imports included, prints SOME PROOFS FAIL (bend
# 2.0.32), so this file and PROOF.bend import src/stop.bend, never main.bend.
import Base
import ./src/stop.bend as Stop
import ./src/args.bend as Args

# LAW: a line goes to stdout, with a newline
law say_line:
  for text: String
  {Stop.say(Args.Line{}, text) == IO.print(text) : IO(Unit)}

# LAW: a page goes to stdout as it is
law say_page:
  for text: String
  {Stop.say(Args.Page{}, text) == IO.write(text) : IO(Unit)}

# LAW: an error goes to stderr
law say_err:
  for text: String
  {Stop.say(Args.Err{}, text) == IO.print_err(text) : IO(Unit)}

# LAW: code 0 falls through
law leave_zero:
  for +code: U32
  for h: {U32.is_eq(code, 0) == True{} : Bool}
  {Stop.leave(code) == IO.pure(Unit, Unit{}) : IO(Unit)}

# LAW: any other code ends the run with it, and says nothing
law leave_code:
  for +code: U32
  for h: {U32.is_eq(code, 0) == False{} : Bool}
  {Stop.leave(code) == IO.die(Unit, code, "") : IO(Unit)}
