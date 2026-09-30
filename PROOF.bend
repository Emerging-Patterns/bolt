# bolt: the proofs of LAWS.bend. `bend PROOF.bend` is the gate.
import Base
import ./src/say.bend as Say
import ./src/args.bend as Args
import ./LAWS.bend as Laws

def Laws.say_line(_text):
  {==}

def Laws.say_page(_text):
  {==}

def Laws.say_err(_text):
  {==}

def Laws.leave_zero(code, h):
  e = Equal.sym(Bool, U32.is_eq(code, 0), True{}, h)
  %e : {Say.leave.at(_, code) == IO.pure(Unit, Unit{}) : IO(Unit)}
  {==}

def Laws.leave_code(code, h):
  e = Equal.sym(Bool, U32.is_eq(code, 0), False{}, h)
  %e : {Say.leave.at(_, code) == IO.die(Unit, code, "") : IO(Unit)}
  {==}
