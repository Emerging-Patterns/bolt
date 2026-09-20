# lazy: each branch runs one side only. The untaken side is a call that
# would never stop on its own budget, so a test that prints at all proves
# it was not run.
import Base
import ../lazy.bend as Lazy
import ../../core/check/kit.bend as Check
import ../../core/check/print.bend as Report

# n steps of work, counting down
def burn(n: Nat, +acc: U32) -> U32:
  match n:
    case 0n:
      acc
    case 1n+m:
      burn(m, (acc + 1 : U32))

# the first cell equal to key, stopping there
def find(xs: List<&2, U32>, +key: U32) -> U32:
  match xs:
    case Nil{}:
      0
    case Con{+h, t}:
      Lazy.stop(U32, U32.is_eq(h, key), h, _u => find(t, key))

# n cells, counting down from n
def big(n: Nat, +k: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+m:
      big(m, (k + 1 : U32), k <> acc)

def main() -> IO(Unit):
  do IO<Unit>:
    Check.eq_u32(~Report.new(), "stop: the hit, the other side untouched",
      Lazy.stop(U32, True{}, 7, _u => burn(U32.to_nat(100000), 0)), 7)
    Check.eq_u32(~Report.new(), "stop: no hit, the thunk gives the answer",
      Lazy.stop(U32, False{}, 7, _u => 9), 9)
    Check.eq_u32(~Report.new(), "stop: a search exits at the first cell",
      find(big(U32.to_nat(2000), 0, []), 1999), 1999)
    Check.eq_u32(~Report.new(), "or_else: True stops",
      Bool.to_u32(Lazy.or_else(True{}, _u => U32.is_eq(burn(U32.to_nat(100000), 0), 0))), 1)
    Check.eq_u32(~Report.new(), "or_else: False asks the thunk",
      Bool.to_u32(Lazy.or_else(False{}, _u => True{})), 1)
    Check.eq_u32(~Report.new(), "and_then: False stops",
      Bool.to_u32(Lazy.and_then(False{}, _u => U32.is_eq(burn(U32.to_nat(100000), 0), 0))), 0)
    Check.eq_u32(~Report.new(), "and_then: True asks the thunk",
      Bool.to_u32(Lazy.and_then(True{}, _u => True{})), 1)

#|ok stop: the hit, the other side untouched
#|ok stop: no hit, the thunk gives the answer
#|ok stop: a search exits at the first cell
#|ok or_else: True stops
#|ok or_else: False asks the thunk
#|ok and_then: False stops
#|ok and_then: True asks the thunk
