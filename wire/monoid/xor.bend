# monoid/xor: 0 and xor
import Base
import ./service.bend as S

def new() -> S.Monoid:
  S.Monoid{0, U32.xor}
