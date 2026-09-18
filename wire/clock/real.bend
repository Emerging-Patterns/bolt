# clock/real: the host's clock
import Base
import ./service.bend as S

# the wall clock
def now(_u: Unit) -> IO(Nat):
  IO.now()

# the real clock
def new() -> S.Clock:
  S.Clock{now}
