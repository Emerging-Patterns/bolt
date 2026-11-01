# proofs of laws/NoqaBare.bend
import Base
import ../src/noqa.bend as Noqa
import ../laws/NoqaBare.bend as Laws
import ../laws/defs/NoqaSpacing.bend as D1

# spaces then any text: the leading spaces are skipped
law nqp.lead:
  for n: Nat
  for +w: String
  {Noqa.lead(D1.nq.spaces(n) ++ w) == Noqa.lead(w) : String}

def nqp.lead(n, w):
  match n:
    case 0n:
      {==}
    case 1n+p:
      nqp.lead(p, w)

def Laws.noqa_bare(line, col, len, n):
  Equal.cong(String, List<&2, Noqa.Mark>, ss => Noqa.mark.word(line, col, len, ss),
    Noqa.lead(D1.nq.spaces(n) ++ "noqa"), Noqa.lead("noqa"), nqp.lead(n, "noqa"))
