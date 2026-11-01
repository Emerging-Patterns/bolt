# part of: laws/NoqaSilencesNamedFindings.bend,
# laws/NoqaReportsStaleComments.bend
import Base
import ../src/noqa.bend as Noqa
import ./defs/NoqaSpacing.bend as D1

# LAW: a comment that is `#`, any number of spaces and `noqa` is one bare
# mark, naming no code
law noqa_bare:
  for line: U32
  for col: U32
  for len: U32
  for n: Nat
  {Noqa.mark.text(line, col, len, "#" ++ D1.nq.spaces(n) ++ "noqa") == [Noqa.Mark{line, col, len, []}]
    : List<&2, Noqa.Mark>}
