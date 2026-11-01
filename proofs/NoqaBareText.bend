# proofs of laws/NoqaBareText.bend
import Base
import ../src/noqa.bend as Noqa
import ../laws/NoqaBareText.bend as Laws
import ../laws/defs/NoqaSpacing.bend as D1
import ./lemmas/NoqaLeadingSpaces.bend as M1

def Laws.noqa_bare_text(line, col, len, n, tt):
  Equal.cong(String, List<&2, Noqa.Mark>, ss => Noqa.mark.word(line, col, len, ss),
    Noqa.lead(D1.nq.spaces(n) ++ "noqa " ++ tt), Noqa.lead("noqa " ++ tt), M1.nqp.lead3(n, "noqa ", tt))
