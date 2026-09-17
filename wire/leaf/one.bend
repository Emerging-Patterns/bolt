# leaf/one: 1 at every index
import Base
import ./service.bend as S

def at(+i: U32) -> U32:
  1

def new() -> S.Leaf:
  S.Leaf{at}
