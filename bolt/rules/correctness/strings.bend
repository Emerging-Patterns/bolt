# rule strings: a `match` whose arms are string literals (`case "foo":`) with
# more than 64 literal characters in all. Each string arm lowers into nested
# per-char tests, and the checker's time and memory grow with the characters
# (bend 2.0.16: 45 characters take 0.8 s and 0.35 GB, 100 take 2 s and 1 GB,
# 480 take 12 s and 4.8 GB; pi-bend BEND-001/016 was 16 long event names).
# The number of arms barely matters, so only the characters count. Classify
# the string once through a lookup table into a sum type, and match on that.
import Base
import ../../src.bend as Src
import ../../finding.bend as F
import ../../../syntax/lex.bend as Lex
import ../../../syntax/tree.bend as Tree
import ../../../lazy/lazy.bend as Lazy
import ../tokens.bend as T

# the string arms of a match, and their characters
type Tally is Data:
  Tally{arms: U32, chars: U32}

# the characters of the string a case pattern opens with, if it does
def literal(kids: Tree.Node) -> Maybe<&2, U32>:
  match kids:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TStr{}, t, l, c}}, rest}:
      +w = T.width(t)
      Some{(w - 2 : U32)}
    case other:
      None{}

# one for a string arm, else zero
def one(mm: Maybe<&2, U32>) -> U32:
  match mm:
    case None{}:
      0
    case Some{n}:
      1

# a string arm's characters, else zero
def size(mm: Maybe<&2, U32>) -> U32:
  match mm:
    case None{}:
      0
    case Some{n}:
      n

# the string arms among a match's statements
def tally(body: Tree.Node, +nn: U32, +chars: U32) -> Tally:
  match body:
    case Tree.NCons{Tree.Stmt{Tree.SCase{}, kids, b}, rest}:
      +m = literal(T.pattern(kids))
      +k = one(m)
      +ch = size(m)
      tally(rest, (nn + k : U32), (chars + ch : U32))
    case Tree.NCons{h, rest}:
      tally(rest, nn, chars)
    case other:
      Tally{nn, chars}

# a finding when the match's strings are too long in all
def report(tt: Tally, +path: String, +ll: U32, +cc: U32) -> List<&2, F.Finding>:
  Tally{+n, +chars} = tt
  Bool.pick(List<&2, F.Finding>, U32.is_gt(chars, 64),
    [F.Finding{path, ll, cc, 5, "strings", "a match over " ++ U32.show(n) ++ " string literals (" ++ U32.show(chars)
      ++ " characters) blows up compile time and memory; map the string to a sum type once (a lookup table)"}],
    [])

# a statement: a match is tallied
def on_stmt(+kids: Tree.Node, +body: Tree.Node, +path: String) -> List<&2, F.Finding>:
  +hit = T.keyword(kids, "match")
  Lazy.stop(List<&2, F.Finding>, Bool.not(hit), [],
    _u => report(tally(body, 0, 0), path, Tree.line(kids), Tree.col(kids)))

# every statement, at any depth
def walk(nn: Tree.Node, +path: String) -> List<&2, F.Finding>:
  match nn:
    case Tree.NCons{Tree.Stmt{kind, kids, +body}, rest}:
      List.concat(&2, F.Finding, [on_stmt(kids, body, path), walk(body, path), walk(rest, path)])
    case Tree.NCons{h, rest}:
      walk(rest, path)
    case other:
      Nil{}

# the rule
def check(ss: Src.Src) -> List<&2, F.Finding>:
  Src.Src{path, text, toks, tree, bound, items} = ss
  walk(tree, path)
