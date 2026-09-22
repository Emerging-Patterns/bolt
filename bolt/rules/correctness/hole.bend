# rule hole: a `?TODO` left in code. LAWS.bend is exempt: by convention its
# laws are open claims, filled by PROOF.bend beside it.
import Base
import ../../src.bend as Src
import ../../finding.bend as F
import ../../../syntax/lex.bend as Lex
import ../../../lazy/lazy.bend as Lazy

def check.go(toks: List<&2, Lex.Tok>, +path: String) -> List<&2, F.Finding>:
  match toks:
    case Con{Lex.Tok{Lex.TOp{}, +q, l, c}, Con{Lex.Tok{Lex.TUpper{}, +t, l2, c2}, rest}}:
      +more = check.go(rest, path)
      Bool.pick(List<&2, F.Finding>, Bool.and(String.eq(q, "?"), String.eq(t, "TODO")),
        F.Finding{path, l, c, 5, "hole", "a ?TODO is left here"} <> more, more)
    case Con{h, rest}:
      check.go(rest, path)
    case Nil{}:
      Nil{}

# the rule
def check(ss: Src.Src) -> List<&2, F.Finding>:
  Src.Src{+path, text, toks, tree, bound, items} = ss
  Lazy.stop(List<&2, F.Finding>, String.ends_with(path, "LAWS.bend"), [], _u => check.go(toks, path))
