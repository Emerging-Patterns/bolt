# checker: an effect service: the diagnostics of the file at a path.
import Base
import ../report.bend as Rep

type Checker is Type:
  Checker{check: String -> IO(List<&2, Rep.Diag>)}

def check(c: Checker, path: String) -> IO(List<&2, Rep.Diag>):
  Checker{f} = c
  f(path)
