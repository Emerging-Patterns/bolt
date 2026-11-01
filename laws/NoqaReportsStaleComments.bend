# `noqa` reports exactly, at each noqa comment's line and column (laws/NoqaSilencesNamedFindings.bend),
# one finding for a bare one (`#`, any spaces, then `noqa` at the comment's
# end or before a space) and one for each code it names that no graded finding
# of its file on its line has, a code that is no rule's included, where a
# project rule's code (`coverage`, `unsafe`) is judged only when the
# run is the whole tree and never in the editor, and nothing else. It runs
# after the filter, over the findings of every other rule, so its findings
# come last (laws/OutputOrderIsFixed.bend) and no noqa comment silences them: a `# noqa: S005`
# silences nothing and is itself reported.
#
# also rests on: laws/NoqaBare.bend, laws/NoqaBareText.bend
import Base
import ../src/finding.bend as F
import ../src/codes.bend as Codes
import ../src/noqa.bend as Noqa
import ../src/rules/style/noqa.bend as NoqaRule

# some graded finding at the path, on the line, has the code
def nq.used(gs: List<&2, F.Graded>, +path: String, +line: U32, +code: String) -> Bool:
  match gs:
    case Nil{}:
      False{}
    case Con{F.Graded{_ll, F.Finding{p, l, _col, _len, rule, _msg}}, rest}:
      Bool.or(Bool.and(String.eq(p, path), Bool.and(U32.is_eq(l, line), String.eq(Codes.code(rule), code))),
        nq.used(rest, path, line, code))

# a project rule's code: `coverage` or `unsafe`'s
def nq.project(+code: String) -> Bool:
  Bool.or(String.eq(code, "L001"), String.eq(code, "L003"))

# how many of a mark's codes the run judges (any over the whole tree, no
# project rule's otherwise) and silence nothing on its line
def nq.unused(cs: List<&2, String>, +whole: Bool, +path: String, +line: U32, +gs: List<&2, F.Graded>) -> Nat:
  match cs:
    case Nil{}:
      0n
    case Con{+c, rest}:
      +m = nq.unused(rest, whole, path, line, gs)
      Bool.pick(Nat, Bool.and(Bool.or(whole, Bool.not(nq.project(c))), Bool.not(nq.used(gs, path, line, c))),
        1n+m, m)

# how many findings a mark earns: one when bare, else one per code unused
def nq.earns(mk: Noqa.Mark, +whole: Bool, +path: String, +gs: List<&2, F.Graded>) -> Nat:
  match mk:
    case Noqa.Mark{_line, _col, _len, Nil{}}:
      1n
    case Noqa.Mark{line, _col, _len, Con{c, rest}}:
      nq.unused(c <> rest, whole, path, line, gs)

# how many findings the marks earn
def nq.count(mks: List<&2, Noqa.Mark>, +whole: Bool, +path: String, +gs: List<&2, F.Graded>) -> Nat:
  match mks:
    case Nil{}:
      0n
    case Con{mk, rest}:
      Nat.add(nq.earns(mk, whole, path, gs), nq.count(rest, whole, path, gs))

# LAW: over a file's marks and the run's graded findings, `noqa` reports one
# finding for each bare mark and one for each code a mark names that the run
# judges and that no graded finding of the file on the mark's line has (a
# code that is no rule's never matches one), and nothing else
law noqa_counts:
  for mks: List<&2, Noqa.Mark>
  for +whole: Bool
  for +path: String
  for +gs: List<&2, F.Graded>
  {List.length(&2, F.Finding, NoqaRule.check(mks, whole, path, gs)) == nq.count(mks, whole, path, gs) : Nat}
