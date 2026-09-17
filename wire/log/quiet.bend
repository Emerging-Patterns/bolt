# log/quiet: drops the line
import Base
import ./service.bend as S

def say(text: String) -> IO(Unit):
  IO.pure(Unit, Unit{})

def new() -> S.Log:
  S.Log{say}
