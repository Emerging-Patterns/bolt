import Base
import ../src/stop.bend as Stop

# LAW: any other code ends the run with it, and says nothing: it is
# `IO.exit`, which writes to no stream (an `IO.die` with an empty message
# still ends its message with a newline on stderr)
law leave_code:
  for +code: U32
  for h: {U32.is_eq(code, 0) == False{} : Bool}
  {Stop.leave(code) == IO.exit(code) : IO(Unit)}
