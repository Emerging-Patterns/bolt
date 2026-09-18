# check/print: "ok name" or "FAIL name" on stdout
import Base
import ./service.bend as S

# `ok name`
def pass(name: String) -> IO(Unit):
  IO.print("ok " ++ name)

# `FAIL name`
def fail(name: String) -> IO(Unit):
  IO.print("FAIL " ++ name)

# the reporter that prints
def new() -> S.Reporter:
  S.Reporter{pass, fail}
