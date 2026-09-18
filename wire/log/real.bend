# log/real: prints the line
import Base
import ./service.bend as S

# the log that prints
def new() -> S.Log:
  S.Log{IO.print}
