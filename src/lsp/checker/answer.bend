# checker/answer: pure: what a run of the checker (bend.bend) gave for a file,
# read from the text bend.bend's exec returns, and the checker as a service.
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

# a run a signal cut short: what bend reported before it died, or, when that
# is nothing, no check at all
def died(ds: List<&2, Rep.Diag>) -> Answer:
  match ds:
    case Nil{}:
      Unrun{}
    case Con{dd, rest}:
      Checked{dd <> rest}

# the answer a tag gives: bend ran (`r`), a signal killed it (`s`), or
# neither, and it could not be run; each error placed by the checked file's
# names, when they are known
def answer.tag(ran: Bool, killed: Bool, names: Maybe<&2, List<&2, String>>, text: String) -> Answer:
  match ran killed:
    case True{} _k:
      Checked{Rep.parse_in(names, text)}
    case False{} True{}:
      died(Rep.parse_in(names, text))
    case False{} False{}:
      Unrun{}

# exec's text read: its tag, then what bend printed, as diagnostics placed by
# the checked file's names
def answer(names: Maybe<&2, List<&2, String>>, ss: String) -> Answer:
  match ss:
    case SNil{}:
      Unrun{}
    case SCon{+cc, text}:
      answer.tag(Char.is_eq(cc, 'r'), Char.is_eq(cc, 's'), names, text)

# a LAWS.bend's errors, settled by its PROOF.bend's answer: none when that
# checks clean, and no check at all when bend could not be run on it
def proved(aa: Answer, ds: List<&2, Rep.Diag>) -> Answer:
  match aa:
    case Checked{pds}:
      Checked{Bool.pick(List<&2, Rep.Diag>, List.is_empty(&2, Rep.Diag, pds), [], ds)}
    case Unrun{}:
      Unrun{}

# effect service: the checker's answer for the file at a path (bend.bend's
# service is the real one)
type Checker is Type:  # noqa: L001 effect service
  Checker{run: String -> IO(Answer)}

# the checker's answer for the file at a path, from a checker service
def check(cc: Checker, path: String) -> IO(Answer):  # noqa: L001 effect accessor
  Checker{r} = cc
  r(path)
