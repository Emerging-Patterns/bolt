# log/quiet: drops the line
import Base
import ./service.bend as S

# nothing
def say(_text: String) -> IO(Unit):
  IO.pure(Unit, Unit{})

# the log that drops everything
def new() -> S.Log:
  S.Log{say}
