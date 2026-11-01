# an early exit to no findings counts zero in the put rule
import Base
import ../../src/finding.bend as F
import ../../src/lazy/lazy.bend as Lazy

# an early exit to no findings counts 0, else what the rest counts
law put.stop:
  for b: Bool
  for -more: List<&2, F.Finding>
  for -m: Nat
  for ih: {List.length(&2, F.Finding, more) == m : Nat}
  {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, b, [], _u => more)) == Bool.pick(Nat, b, 0n, m) : Nat}

def put.stop(b, _more, _m, ih):
  match b:
    case True{}:
      {==}
    case False{}:
      ih
