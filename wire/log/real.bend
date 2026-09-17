# log/real: prints the line
import Base
import ./service.bend as S

def new() -> S.Log:
  S.Log{IO.print}
