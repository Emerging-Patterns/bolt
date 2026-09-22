# leaf/index: i at index i
import Base
import ./service.bend as S

# the index itself
def at(+ii: U32) -> U32:
  ii

# the leaf that is its index
def new() -> S.Leaf:
  S.Leaf{at}
