# checker/fake: a path with "bad" in it has one error on line 3; others are clean
import Base
import ./service.bend as S
import ../report.bend as Rep

def check(path: String) -> IO(List<&2, Rep.Diag>):
  IO.pure(List<&2, Rep.Diag>, Bool.pick(List<&2, Rep.Diag>, String.contains(path, "bad"),
    [Rep.Diag{3, "expected : String\nobserved : U32"}], []))

def new() -> S.Checker:
  S.Checker{check}
