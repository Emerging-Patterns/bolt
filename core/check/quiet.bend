# check/quiet: says nothing
import Base
import ./service.bend as S

# nothing
def say(_name: String) -> IO(Unit):
  IO.pure(Unit, Unit{})

# the reporter that says nothing
def new() -> S.Reporter:
  S.Reporter{say, say}
