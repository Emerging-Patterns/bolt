# rule noqa: a noqa comment (src/noqa.bend) that silences nothing, as
# ruff's RUF100. A bare one names no code, so it silences nothing; a code
# it names silences nothing when no graded finding of the file, on the
# mark's line, has that code, and a code that is no rule's never does. One
# finding for a bare mark, and one for each such code, at the comment.
#
# It reads the graded findings of the whole run, so it is no per-file rule:
# the planner runs it after every other rule and after the filter, and
# what it reports no noqa comment silences. A project rule's code
# (`coverage`, `unsafe`, `trace`) is judged only when the run is the whole
# tree (`whole`): over files named, and in the editor, those rules see only
# part of the laws, so their silence proves nothing.
import Base
import ../../lazy/lazy.bend as Lazy
import ../../finding.bend as F
import ../../codes.bend as Codes
import ../../noqa.bend as Noqa

# a project rule's code
def project(+code: String) -> Bool:
  Lazy.or_else(String.eq(code, Codes.code("coverage")),
    _u => Lazy.or_else(String.eq(code, Codes.code("unsafe")), _v => String.eq(code, Codes.code("trace"))))

# a code this run can judge: any, over the whole tree; a per-file rule's
# (or no rule's) otherwise
def judged(+whole: Bool, +code: String) -> Bool:
  Lazy.or_else(whole, _u => Bool.not(project(code)))

# some row of the table has the code
def known.in(rows: List<&2, Codes.Entry>, +code: String) -> Bool:
  match rows:
    case Nil{}:
      False{}
    case Con{Codes.Entry{_s, id, _grp}, rest}:
      Lazy.or_else(String.eq(id, code), _u => known.in(rest, code))

# the code is a rule's
def known(+code: String) -> Bool:
  known.in(Codes.table(), code)

# a graded finding at the path, on the line, has the code
def used(gs: List<&2, F.Graded>, +path: String, +line: U32, +code: String) -> Bool:
  match gs:
    case Nil{}:
      False{}
    case Con{F.Graded{_ll, F.Finding{p, l, _col, _len, rule, _msg}}, rest}:
      Lazy.or_else(
        Lazy.and_then(String.eq(p, path),
          _u => Lazy.and_then(U32.is_eq(l, line), _v => String.eq(Codes.code(rule), code))),
        _w => used(rest, path, line, code))

# what a bare mark is told
def say.bare() -> String:
  "`# noqa` names no code, so it silences nothing; name the codes, e.g. `# noqa: L001`."

# what an unused code is told: a rule's, or no rule's
def say(+code: String) -> String:
  Bool.pick(String, known(code), "`# noqa: " ++ code ++ "` silences nothing on this line.",
    "`# noqa: " ++ code ++ "` is no rule's code, so it silences nothing.")

# one finding for each code judged here that silences nothing on its line
def check.codes(
  cs: List<&2, String>,
  +whole: Bool,
  +path: String,
  +line: U32,
  +col: U32,
  +len: U32,
  +gs: List<&2, F.Graded>
) -> List<&2, F.Finding>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{+c, rest}:
      +more = check.codes(rest, whole, path, line, col, len, gs)
      +bad = Lazy.and_then(judged(whole, c), _u => Bool.not(used(gs, path, line, c)))
      +msg = say(c)
      Bool.pick(List<&2, F.Finding>, bad, F.Finding{path, line, col, len, "noqa", msg} <> more, more)

# a mark's findings: one when it is bare, else one per code that silences
# nothing
def check.mark(mk: Noqa.Mark, +whole: Bool, +path: String, +gs: List<&2, F.Graded>) -> List<&2, F.Finding>:
  match mk:
    case Noqa.Mark{line, col, len, Nil{}}:
      [F.Finding{path, line, col, len, "noqa", say.bare()}]
    case Noqa.Mark{line, col, len, Con{c, rest}}:
      check.codes(c <> rest, whole, path, line, col, len, gs)

# every mark of the file at the path, against the run's graded findings
def check(mks: List<&2, Noqa.Mark>, +whole: Bool, +path: String, +gs: List<&2, F.Graded>) -> List<&2, F.Finding>:
  match mks:
    case Nil{}:
      Nil{}
    case Con{mk, rest}:
      List.append(&2, F.Finding, check.mark(mk, whole, path, gs), check(rest, whole, path, gs))
