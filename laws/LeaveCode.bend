import Base
import ../src/stop.bend as Stop

# LAW: any other code ends the run with it, and says nothing
law leave_code:
  for +code: U32
  for h: {U32.is_eq(code, 0) == False{} : Bool}
  {Stop.leave(code) == IO.die(Unit, code, "") : IO(Unit)}
