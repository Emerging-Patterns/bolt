# skipping leading spaces then a word in noqa comment parsing
import Base
import ../../src/noqa.bend as Noqa
import ../../laws/defs/NoqaSpacing.bend as D1

# spaces, a word, then any text: the leading spaces are skipped
law nqp.lead3:
  for n: Nat
  for +w: String
  for +tt: String
  {Noqa.lead(D1.nq.spaces(n) ++ w ++ tt) == Noqa.lead(w ++ tt) : String}

def nqp.lead3(n, w, tt):
  match n:
    case 0n:
      {==}
    case 1n+p:
      nqp.lead3(p, w, tt)
