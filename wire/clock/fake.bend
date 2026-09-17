# clock/fake: always 42
import Base
import ./service.bend as S

def now(u: Unit) -> IO(Nat):
  IO.pure(Nat, 42n)

def new() -> S.Clock:
  S.Clock{now}
