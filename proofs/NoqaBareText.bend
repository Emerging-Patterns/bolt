# proofs of laws/NoqaBareText.bend
import Base
import ../src/noqa.bend as Noqa
import ../laws/NoqaBareText.bend as Laws
import ../laws/defs/NoqaSpacing.bend as D1
import ./lemmas/NoqaLeadingSpaces.bend as M1

def Laws.noqa_bare_text(line, col, len, n, t):
  Equal.cong(String, List<&2, Noqa.Mark>, s => Noqa.mark.word(line, col, len, s),
    Noqa.lead(D1.nq.spaces(n) ++ "noqa " ++ t), Noqa.lead("noqa " ++ t), M1.nqp.lead3(n, "noqa ", t))
