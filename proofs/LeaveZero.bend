# proofs of laws/LeaveZero.bend
import Base
import ../src/stop.bend as Stop
import ../laws/LeaveZero.bend as Laws

def Laws.leave_zero(code, h):
  e = Equal.sym(Bool, U32.is_eq(code, 0), True{}, h)
  %e : {Stop.leave.at(_, code) == IO.pure(Unit, Unit{}) : IO(Unit)}
  {==}
