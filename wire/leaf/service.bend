# leaf: a pure service (GPU-safe): the value at index i.
import Base

# pure service: the value at an index of a range
type Leaf is Type:
  Leaf{at: @+i:U32 -> U32}

# the value at an index, from a leaf
def at(l: Leaf, i: U32) -> U32:
  Leaf{f} = l
  f(i)
