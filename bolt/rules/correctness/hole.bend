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
import ../calls.bend as Calls

# True when the first token past spaces, newlines and comments is `TODO`
def check.todo(toks: List<&2, Lex.Tok>) -> Bool:
  match toks:
    case Con{Lex.Tok{+k, +t, l, c}, rest}:
      Lazy.stop(Bool, Lex.significant(k), Bool.and(Calls.kind.upper(k), String.eq(t, "TODO")), _u => check.todo(rest))
    case Nil{}:
      False{}

# the width of the hole a `?` at line, col starts: through the next token
# past spaces, newlines and comments when it sits on the same line, else 1
def check.width(toks: List<&2, Lex.Tok>, +line: U32, +col: U32) -> U32:
  match toks:
    case Con{Lex.Tok{k, t, +l, +c}, rest}:
      Lazy.stop(U32, Lex.significant(k), Bool.pick(U32, U32.is_eq(l, line), U32.add(U32.sub(c, col), 4), 1),
        _u => check.width(rest, line, col))
    case Nil{}:
      1

def check.go(toks: List<&2, Lex.Tok>, +path: String) -> List<&2, F.Finding>:
  match toks:
    case Con{Lex.Tok{k, +q, +l, +c}, +rest}:
      +more = check.go(rest, path)
      Lazy.stop(List<&2, F.Finding>, Bool.not(Bool.and(Calls.kind.oper(k), Lazy.and_then(String.eq(q, "?"),
        _u => check.todo(rest)))), more,
        _u => F.Finding{path, l, c, check.width(rest, l, c), "hole", "This ?TODO hole is still unfilled."} <> more)
    case Nil{}:
      Nil{}

def check.on(toks: List<&2, Lex.Tok>, +path: String) -> List<&2, F.Finding>:
  Lazy.stop(List<&2, F.Finding>, Paths.is_laws(path), [], _u => check.go(toks, path))

# the rule
def check(ss: Src.Src) -> List<&2, F.Finding>:
  Src.Src{path, text, toks, tree, bound, items} = ss
  check.on(toks, path)
