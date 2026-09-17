# check/print: "ok name" or "FAIL name" on stdout
import Base
import ./service.bend as S

def pass(name: String) -> IO(Unit):
  IO.print("ok " ++ name)

def fail(name: String) -> IO(Unit):
  IO.print("FAIL " ++ name)

def new() -> S.Reporter:
  S.Reporter{pass, fail}
