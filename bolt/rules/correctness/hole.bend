# rule hole: a TODO hole left in code, the one bend counts in "N TODO found":
# a `?` and then the name `TODO`, with any spaces, newlines or comments
# between them (`?TODO`, `? TODO`). `?todo`, `?TODO_later` and `?TODO.x` are
# other names, which bend reports as a type error, not as a TODO, and they are
# not reported here. The finding spans `?` through `TODO` when both sit on one
# line, and the `?` alone when `TODO` is on a later line. LAWS.bend is exempt:
# by convention its laws are open claims, filled by PROOF.bend beside it.
import Base
import ../../paths.bend as Paths
import ../../src.bend as Src
import ../../finding.bend as F
import ../../../syntax/lex.bend as Lex
import ../../../lazy/lazy.bend as Lazy

# the width of the hole a `?` at line, col starts, when the first token past
# spaces, newlines and comments is `TODO`; 0 when it is anything else
def check.width(toks: List<&2, Lex.Tok>, +line: U32, +col: U32) -> U32:
  match toks:
    case Con{Lex.Tok{Lex.TSpace{}, t, l, c}, rest}:
      check.width(rest, line, col)
    case Con{Lex.Tok{Lex.TNewline{}, t, l, c}, rest}:
      check.width(rest, line, col)
    case Con{Lex.Tok{Lex.TComment{}, t, l, c}, rest}:
      check.width(rest, line, col)
    case Con{Lex.Tok{Lex.TUpper{}, +t, +l, +c}, rest}:
      Bool.pick(U32, String.eq(t, "TODO"),
        Bool.pick(U32, U32.is_eq(l, line), U32.add(U32.sub(c, col), 4), 1), 0)
    case other:
      0

def check.go(toks: List<&2, Lex.Tok>, +path: String) -> List<&2, F.Finding>:
  match toks:
    case Con{Lex.Tok{Lex.TOp{}, +q, +l, +c}, +rest}:
      +more = check.go(rest, path)
      +ww = Lazy.stop(U32, Bool.not(String.eq(q, "?")), 0, _u => check.width(rest, l, c))
      Bool.pick(List<&2, F.Finding>, U32.is_gt(ww, 0),
        F.Finding{path, l, c, ww, "hole", "A ?TODO is left here."} <> more, more)
    case Con{h, rest}:
      check.go(rest, path)
    case Nil{}:
      Nil{}

# the rule
def check(ss: Src.Src) -> List<&2, F.Finding>:
  Src.Src{+path, text, toks, tree, bound, items} = ss
  Lazy.stop(List<&2, F.Finding>, Paths.is_laws(path), [], _u => check.go(toks, path))
