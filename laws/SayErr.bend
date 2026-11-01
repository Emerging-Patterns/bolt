import Base
import ../src/stop.bend as Stop
import ../src/args.bend as Args

# LAW: an error goes to stderr
law say_err:
  for text: String
  {Stop.say(Args.Err{}, text) == IO.print_err(text) : IO(Unit)}
