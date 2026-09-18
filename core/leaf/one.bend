# leaf/one: 1 at every index
import Base
import ./service.bend as S

# always 1
def at(+_i: U32) -> U32:
  1

# the leaf that is 1 everywhere (a fold counts)
def new() -> S.Leaf:
  S.Leaf{at}
