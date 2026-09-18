# checker: an effect service: the diagnostics of the file at a path.
import Base
import ../report.bend as Rep

# effect service: a file's diagnostics
type Checker is Type:
  Checker{check: String -> IO(List<&2, Rep.Diag>)}

# a file's diagnostics, from a checker
def check(c: Checker, path: String) -> IO(List<&2, Rep.Diag>):
  Checker{f} = c
  f(path)
