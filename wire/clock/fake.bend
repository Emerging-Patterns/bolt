# clock/fake: always 42
import Base
import ./service.bend as S

# always 42
def now(_u: Unit) -> IO(Nat):
  IO.pure(Nat, 42n)

# the clock stuck at 42
def new() -> S.Clock:
  S.Clock{now}
