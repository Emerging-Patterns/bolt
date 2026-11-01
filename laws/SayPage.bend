import Base
import ../src/stop.bend as Stop
import ../src/args.bend as Args

# LAW: a page goes to stdout as it is
law say_page:
  for text: String
  {Stop.say(Args.Page{}, text) == IO.write(text) : IO(Unit)}
