# leaf: a pure service (GPU-safe): the value at index i.
import Base

type Leaf is Type:
  Leaf{at: @+i:U32 -> U32}

def at(l: Leaf, i: U32) -> U32:
  Leaf{f} = l
  f(i)
