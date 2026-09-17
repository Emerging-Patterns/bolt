# check/quiet: says nothing
import Base
import ./service.bend as S

def say(name: String) -> IO(Unit):
  IO.pure(Unit, Unit{})

def new() -> S.Reporter:
  S.Reporter{say, say}
