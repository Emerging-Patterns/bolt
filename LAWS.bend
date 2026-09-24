# bolt: the laws of main.bend's own defs. main.bend only does what Args.out
# decides (src/LAWS.bend states that decision for every argv). A text goes to
# its stream, and a code exits as it says. dispatch, perform and main have no
# law here: each reaches the linter's, checker's or server's foreign IO, and a
# proof that reaches foreign code does not print a clean "All terms check."
import Base
import ./main.bend as Main
import ./src/args.bend as Args

# LAW: a line goes to stdout, with a newline
law say_line:
  for text: String
  {Main.say(Args.Line{}, text) == IO.print(text) : IO(Unit)}

# LAW: a page goes to stdout as it is
law say_page:
  for text: String
  {Main.say(Args.Page{}, text) == IO.write(text) : IO(Unit)}

# LAW: an error goes to stderr
law say_err:
  for text: String
  {Main.say(Args.Err{}, text) == IO.print_err(text) : IO(Unit)}

# LAW: code 0 falls through
law leave_zero:
  for +code: U32
  for h: {U32.is_eq(code, 0) == True{} : Bool}
  {Main.leave(code) == IO.pure(Unit, Unit{}) : IO(Unit)}

# LAW: any other code ends the run with it, and says nothing
law leave_code:
  for +code: U32
  for h: {U32.is_eq(code, 0) == False{} : Bool}
  {Main.leave(code) == IO.die(Unit, code, "") : IO(Unit)}
