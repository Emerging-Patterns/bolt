# par/fold: a parallel fold over an injected Monoid and Leaf. Pure, so
# GPU-safe: call it as Fold.fold!(..) to run on the GPU.
import Base
import ../monoid/service.bend as Monoid
import ../leaf/service.bend as Leaf

# folds leaf(j) for j in [i * 2^n, (i + 1) * 2^n), splitting in two per level
def fold(~m: Monoid.Monoid, ~leaf: Leaf.Leaf, +n: Nat, +i: U32) -> U32:
  match n:
    case 0n:
      Leaf.at(leaf, i)
    case 1n+p:
      a b = fold(~m, ~leaf, p, (i * 2 : U32)) fold(~m, ~leaf, p, (i * 2 + 1 : U32))
      Monoid.join(m, a, b)
