# rule chars: a `match` with more than eight character-literal arms
# (`case '.':`). `Char` is `Chr{code: U32}`, so such an arm is a U32 literal
# inside a constructor pattern, and bend's C backend pays for each one out of
# all proportion to its size -- about 90 MB, and the cost compounds through
# every def downstream of the one holding them (eighteen arms cost 1.57 GB
# and 8.3 s here, 0.10 GB and 0.7 s once rewritten). It is the literals, not
# the arms: a match over eighteen constructors costs nothing measurable.
#
# Compare `Char.to_u32(c)` instead. Bind the fallback above the comparisons
# so it is a value, not a call, or bolt's own `eager` rule fires on it; and
# give the def the reusable quantity (`+c: Char`), since the code point and
# the fallback both consume it. Where the arms carry linear values, leave
# the match alone: a cascade would break linearity and do every branch's
# work.
#
# Only a case's first match column is read, and only an arm whose pattern
# opens with a character literal counts: `case 'x':` does, `case Con{'x', t}:`
# and a literal in a later column of `match a b:` do not.
import Base
import ../../src.bend as Src
import ../../finding.bend as F
import ../../../syntax/lex.bend as Lex
import ../../../syntax/tree.bend as Tree
import ../../../lazy/lazy.bend as Lazy
import ../tokens.bend as T

# one when a case pattern opens with a character literal, else zero
def literal(kids: Tree.Node) -> U32:
  match kids:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TChar{}, t, l, c}}, rest}:
      1
    case other:
      0

# the character-literal arms among a match's statements
def tally(body: Tree.Node, +nn: U32) -> U32:
  match body:
    case Tree.NCons{Tree.Stmt{Tree.SCase{}, kids, b}, rest}:
      +k = literal(T.pattern(kids))
      tally(rest, (nn + k : U32))
    case Tree.NCons{h, rest}:
      tally(rest, nn)
    case other:
      nn

# a finding when the match holds more character literals than is cheap
def report(+nn: U32, +path: String, +ll: U32, +cc: U32) -> List<&2, F.Finding>:
  Bool.pick(List<&2, F.Finding>, U32.is_gt(nn, 8),
    [F.Finding{path, ll, cc, 5, "chars", "This match has " ++ U32.show(nn)
      ++ " character-literal cases, over the limit of 8, which blows up compile time and memory; compare Char.to_u32(c) instead."}],
    [])

# a statement: a match is tallied
def on_stmt(+kids: Tree.Node, +body: Tree.Node, +path: String) -> List<&2, F.Finding>:
  +hit = T.keyword(kids, "match")
  Lazy.stop(List<&2, F.Finding>, Bool.not(hit), [],
    _u => report(tally(body, 0), path, Tree.line(kids), Tree.col(kids)))

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
