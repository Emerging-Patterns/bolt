# checker/bend: the real checker: runs `bend` on the file and reads its report
import Base
import ../../paths.bend as Paths
import ./service.bend as S
import ../report.bend as Rep

# how `bend <path> --check-only` went, one tag char, then everything it
# printed; it checks, and never runs main. The tag is `r` when bend ran and
# exited, `s` when a signal killed it, and `x` when it could not be run: no
# pipe, no fork, or an exit with 127, the code a failed exec exits with (as a
# shell does for a command it cannot find)
def bendcheck.exec(path: String) -> IO(String):
  import "./exec.c"
  import "./exec.js"

# a run a signal cut short: what bend reported before it died, or, when that
# is nothing, no check at all
def died(ds: List<&2, Rep.Diag>) -> S.Answer:
  match ds:
    case Nil{}:
      S.Unrun{}
    case Con{dd, rest}:
      S.Checked{dd <> rest}

# the answer a tag gives: bend ran (`r`), a signal killed it (`s`), or
# neither, and it could not be run
def answer.tag(ran: Bool, killed: Bool, text: String) -> S.Answer:
  match ran killed:
    case True{} _k:
      S.Checked{Rep.parse(text)}
    case False{} True{}:
      died(Rep.parse(text))
    case False{} False{}:
      S.Unrun{}

# exec's text read: its tag, then what bend printed, as diagnostics
def answer(ss: String) -> S.Answer:
  match ss:
    case SNil{}:
      S.Unrun{}
    case SCon{+cc, text}:
      answer.tag(Char.is_eq(cc, 'r'), Char.is_eq(cc, 's'), text)

# only the open-laws report ("N TODOs found"), and nothing else
def only_todos(ds: List<&2, Rep.Diag>) -> Bool:
  match ds:
    case Con{Rep.Diag{line, msg}, Nil{}}:
      String.contains(msg, "TODO found")
    case other:
      False{}

# the PROOF.bend beside a LAWS.bend
def proof_path(+path: String) -> String:
  String.take(path, Nat.sub(String.length(path), 9n)) ++ "PROOF.bend"

# a LAWS.bend's errors, settled by its PROOF.bend's answer: none when that
# checks clean, and no check at all when bend could not be run on it
def proved(aa: S.Answer, ds: List<&2, Rep.Diag>) -> S.Answer:
  match aa:
    case S.Checked{pds}:
      S.Checked{Bool.pick(List<&2, Rep.Diag>, List.is_empty(&2, Rep.Diag, pds), [], ds)}
    case S.Unrun{}:
      S.Unrun{}

# By convention LAWS.bend states its laws as open claims and PROOF.bend, beside
# it, fills them: alone, LAWS.bend always has TODOs. They are an error only
# while PROOF.bend does not check clean.
def settle(open: Bool, +ds: List<&2, Rep.Diag>, path: String) -> IO(S.Answer):
  match open:
    case False{}:
      IO.pure(S.Answer, S.Checked{ds})
    case True{}:
      do IO<S.Answer>:
        text : String <- bendcheck.exec(proof_path(path))
        return proved(answer(text), ds)

# the diagnostics of a run, settled when they are only the open laws of a
# LAWS.bend
def checked(+ds: List<&2, Rep.Diag>, +path: String) -> IO(S.Answer):
  settle(Bool.and(only_todos(ds), Paths.is_laws(path)), ds, path)

# a run's answer: its diagnostics settled when bend ran, else no check
def settled(aa: S.Answer, +path: String) -> IO(S.Answer):
  match aa:
    case S.Checked{ds}:
      checked(ds, path)
    case S.Unrun{}:
      IO.pure(S.Answer, S.Unrun{})

def check.at(+path: String) -> IO(S.Answer):
  do IO<S.Answer>:
    text : String <- bendcheck.exec(path)
    settled(answer(text), path)

# the service's field takes a plain path; quantities are part of its type
def check(path: String) -> IO(S.Answer):
  check.at(path)

# the real checker
def new() -> S.Checker:
  S.Checker{check}
