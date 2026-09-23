# checker/fake: a path with "bad" in it has one error on line 3; others are clean
import Base
import ./service.bend as S
import ../report.bend as Rep

# one error on line 0 when the path contains `bad`, else none
def check(path: String) -> IO(S.Answer):
  IO.pure(S.Answer, S.Checked{Bool.pick(List<&2, Rep.Diag>, String.contains(path, "bad"),
    [Rep.Diag{3, "expected : String\nobserved : U32"}], [])})

# the canned checker
def new() -> S.Checker:
  S.Checker{check}
