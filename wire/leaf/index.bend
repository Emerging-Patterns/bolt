# leaf/index: i at index i
import Base
import ./service.bend as S

# the index itself
def at(+i: U32) -> U32:
  i

# the leaf that is its index
def new() -> S.Leaf:
  S.Leaf{at}
