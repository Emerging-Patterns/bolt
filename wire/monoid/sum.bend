# monoid/sum: 0 and +
import Base
import ./service.bend as S

# addition, with unit 0
def new() -> S.Monoid:
  S.Monoid{0, U32.add}
