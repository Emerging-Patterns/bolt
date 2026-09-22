# par/fold: a parallel fold over an injected Monoid and Leaf. Pure, so
# GPU-safe: call it as Fold.fold!(..) to run on the GPU.
import Base
import ../monoid/service.bend as Monoid
import ../leaf/service.bend as Leaf

# folds leaf(j) for j in [i * 2^n, (i + 1) * 2^n), splitting in two per level
def fold(~mm: Monoid.Monoid, ~leaf: Leaf.Leaf, +nn: Nat, +ii: U32) -> U32:
  match nn:
    case 0n:
      Leaf.at(leaf, ii)
    case 1n+p:
      a b = fold(~mm, ~leaf, p, (ii * 2 : U32)) fold(~mm, ~leaf, p, (ii * 2 + 1 : U32))
      Monoid.join(mm, a, b)
