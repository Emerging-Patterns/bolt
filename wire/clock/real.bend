# clock/real: the host's clock
import Base
import ./service.bend as S

def now(u: Unit) -> IO(Nat):
  IO.now()

def new() -> S.Clock:
  S.Clock{now}
