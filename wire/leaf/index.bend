# leaf/index: i at index i
import Base
import ./service.bend as S

def at(+i: U32) -> U32:
  i

def new() -> S.Leaf:
  S.Leaf{at}
