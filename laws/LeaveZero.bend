import Base
import ../src/stop.bend as Stop

# LAW: code 0 falls through
law leave_zero:
  for +code: U32
  for h: {U32.is_eq(code, 0) == True{} : Bool}
  {Stop.leave(code) == IO.pure(Unit, Unit{}) : IO(Unit)}
