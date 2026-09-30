# checker/bend: pure (GPU-safe): what a run of bend answered. The foreign
# run that produces the text is checker/run.bend; this file only reads it.
import Base
import ./answer.bend as S
import ../report.bend as Rep

# a run a signal cut short: what bend reported before it died, or, when that
# is nothing, no check at all
def died(ds: List<&2, Rep.Diag>) -> S.Answer:
  match ds:
    case Nil{}:
      S.Unrun{}
    case Con{dd, rest}:
      S.Checked{dd <> rest}

# the answer a tag gives: bend ran (`r`), a signal killed it (`s`), or
# neither, and it could not be run; each error placed by the checked file's
# names, when they are known
def answer.tag(ran: Bool, killed: Bool, names: Maybe<&2, List<&2, String>>, text: String) -> S.Answer:
  match ran killed:
    case True{} _k:
      S.Checked{Rep.parse_in(names, text)}
    case False{} True{}:
      died(Rep.parse_in(names, text))
    case False{} False{}:
      S.Unrun{}

# exec's text read: its tag, then what bend printed, as diagnostics placed by
# the checked file's names
def answer(names: Maybe<&2, List<&2, String>>, ss: String) -> S.Answer:
  match ss:
    case SNil{}:
      S.Unrun{}
    case SCon{+cc, text}:
      answer.tag(Char.is_eq(cc, 'r'), Char.is_eq(cc, 's'), names, text)

# a LAWS.bend's errors, settled by its PROOF.bend's answer: none when that
# checks clean, and no check at all when bend could not be run on it
def proved(aa: S.Answer, ds: List<&2, Rep.Diag>) -> S.Answer:
  match aa:
    case S.Checked{pds}:
      S.Checked{Bool.pick(List<&2, Rep.Diag>, List.is_empty(&2, Rep.Diag, pds), [], ds)}
    case S.Unrun{}:
      S.Unrun{}
