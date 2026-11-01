import Base
import ../src/stop.bend as Stop
import ../src/args.bend as Args

# LAW: a line goes to stdout, with a newline
law say_line:
  for text: String
  {Stop.say(Args.Line{}, text) == IO.print(text) : IO(Unit)}
