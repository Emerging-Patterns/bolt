# lazy: the laws. The three branches must agree with the strict ones they
# replace: bolt's `pick` and `strict` rules send people here, and twenty-one
# sites in this repo were rewritten to use them, so an answer that differs
# from Bool.pick, Bool.or or Bool.and would be a silent change of meaning.
import Base
import ./lazy.bend as Lazy

# LAW: a thunk that ignores its argument makes stop Bool.pick
law stop_is_pick:
  for c: Bool
  for a: U32
  for b: U32
  {Lazy.stop(U32, c, a, _u => b) == Bool.pick(U32, c, a, b) : U32}

# LAW: or_else is Bool.or on a constant thunk
law or_else_is_or:
  for a: Bool
  for b: Bool
  {Lazy.or_else(a, _u => b) == Bool.or(a, b) : Bool}

# LAW: and_then is Bool.and on a constant thunk
law and_then_is_and:
  for a: Bool
  for b: Bool
  {Lazy.and_then(a, _u => b) == Bool.and(a, b) : Bool}
