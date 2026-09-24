# checker/answer: pure: what a run of the checker (bend.bend) gave for a file.
import Base
import ../report.bend as Rep

# a checker's answer for a file: the diagnostics bend reported, or that bend
# could not be run on it at all
type Answer is Data:
  Checked{ds: List<&2, Rep.Diag>}
  Unrun{}

# an answer's diagnostics: none when bend could not be run
def errors(aa: Answer) -> List<&2, Rep.Diag>:
  match aa:
    case Checked{ds}:
      ds
    case Unrun{}:
      []
