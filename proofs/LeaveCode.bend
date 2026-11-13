# proofs of laws/LeaveCode.bend
import Base
import ../src/stop.bend as Stop
import ../laws/LeaveCode.bend as Laws

def Laws.leave_code(code, h):
  e = Equal.sym(Bool, U32.is_eq(code, 0), False{}, h)
  %e : {Stop.leave.at(_, code) == IO.exit(code) : IO(Unit)}
  {==}
