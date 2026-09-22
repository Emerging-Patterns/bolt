# rule table: `List.set` at a computed index inside a def that calls itself.
# Setting one cell walks and copies the list, so a fixed table updated on
# every step is quadratic. Keep the table in an Array and use `Array.set`.
# `List.get` / `String.get` stay with `index`: one finding per call. A literal
# index is a fixed slot, not a scan, and laws and proofs do not run.
import Base
import ../../src.bend as Src
import ../../finding.bend as F
import ../../../syntax/lex.bend as Lex
import ../../../syntax/tree.bend as Tree
import ../calls.bend as Calls
import ../../../lazy/lazy.bend as Lazy

# is the chain exactly one number?
def literal(nn: Tree.Node) -> Bool:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TNum{}, t, l, c}}, Tree.NNil{}}:
      True{}
    case other:
      False{}

# every List.set at a computed index
def walk(nn: Tree.Node, +path: String) -> List<&2, F.Finding>:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, +t, +l, +c}}, Tree.NCons{Tree.Group{Lex.Tok{_, +o, _, _}, +kids, _}, rest}}:
      +set = Bool.and(String.eq(o, "("), String.eq(t, "List.set"))
      +fire = Bool.and(set, Bool.not(literal(Calls.arg(Calls.args(kids), 3n))))
      +more = List.concat(&2, F.Finding, [walk(kids, path), walk(rest, path)])
      Bool.pick(List<&2, F.Finding>, fire,
        F.Finding{path, l, c, U32.from_nat(String.length(t)), "table",
          "List.set inside a recursive def copies the list to change one cell; keep the table in an Array and use Array.set."}
          <> more,
        more)
    case Tree.NCons{Tree.Group{open, kids, close}, rest}:
      List.concat(&2, F.Finding, [walk(kids, path), walk(rest, path)])
    case Tree.NCons{Tree.Stmt{kind, kids, body}, rest}:
      List.concat(&2, F.Finding, [walk(kids, path), walk(body, path), walk(rest, path)])
    case Tree.NCons{h, rest}:
      walk(rest, path)
    case other:
      Nil{}

def check.go(ds: List<&2, Calls.Def>, +path: String, acc: List<&2, List<&2, F.Finding>>) -> List<&2, F.Finding>:
  match ds:
    case Nil{}:
      List.concat(&2, F.Finding, List.reverse(&2, List<&2, F.Finding>, acc))
    case Con{Calls.Def{+name, +sig, +body}, rest}:
      check.go(rest, path,
        Lazy.stop(List<&2, F.Finding>,
          Bool.not(Bool.and(Calls.calls(body, name), Bool.not(Calls.exempt(path, sig)))), [],
          _u => walk(body, path)) <> acc)

# the rule
def check(ss: Src.Src) -> List<&2, F.Finding>:
  Src.Src{path, text, toks, tree, bound, items} = ss
  check.go(Calls.defs(tree), path, [])
