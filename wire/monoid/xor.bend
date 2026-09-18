# monoid/xor: 0 and xor
import Base
import ./service.bend as S

# exclusive or, with unit 0
def new() -> S.Monoid:
  S.Monoid{0, U32.xor}
