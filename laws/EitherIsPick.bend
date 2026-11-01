import Base
import ../src/lazy/lazy.bend as Lazy

# LAW: either is Bool.pick on constant thunks
law either_is_pick:
  for c: Bool
  for a: U32
  for b: U32
  {Lazy.either(U32, c, _u => a, _v => b) == Bool.pick(U32, c, a, b) : U32}
