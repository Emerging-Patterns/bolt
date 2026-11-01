# a stop at the first True is Bool.or
import Base
import ../../src/lazy/lazy.bend as Lazy

# a stop at the first True is Bool.or
law unused.or:
  for a: Bool
  for -x: Bool
  for -y: Bool
  for ih: {x == y : Bool}
  {Lazy.or_else(a, _u => x) == Bool.or(a, y) : Bool}

def unused.or(a, _x, _y, ih):
  match a:
    case True{}:
      {==}
    case False{}:
      ih
