# checker: an effect service: the diagnostics of the file at a path.
import Base
import ../report.bend as Rep

# a checker's answer for a file: the diagnostics bend reported, or that bend
# could not be run on it at all
type Answer is Data:
  Checked{ds: List<&2, Rep.Diag>}
  Unrun{}

# effect service: a file's diagnostics
type Checker is Type:
  Checker{check: String -> IO(Answer)}

# a file's diagnostics, from a checker
def check(cc: Checker, path: String) -> IO(Answer):
  Checker{f} = cc
  f(path)

# an answer's diagnostics: none when bend could not be run
def errors(aa: Answer) -> List<&2, Rep.Diag>:
  match aa:
    case Checked{ds}:
      ds
    case Unrun{}:
      []
