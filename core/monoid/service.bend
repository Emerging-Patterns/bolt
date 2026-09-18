# monoid: a pure service (GPU-safe): a unit and an associative join over U32.
# The laws in LAWS.bend are what make a parallel split of a fold legal.
import Base

# pure service: a unit and an associative join over U32
type Monoid is Type:
  Monoid{unit: U32, join: U32 -> U32 -> U32}

# accessors: consumers touch the service only through these
def unit(m: Monoid) -> U32:
  Monoid{u, j} = m
  u

# two values joined, by a monoid
def join(m: Monoid, a: U32, b: U32) -> U32:
  Monoid{u, j} = m
  j(a, b)
