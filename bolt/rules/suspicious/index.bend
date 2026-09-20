# rule index: a def that calls itself also calls `List.get(..)` or
# `String.get(..)`. Both walk the cons list from the head to the index, so a
# per-index loop is quadratic (AppSprout's sort went from 39 s to 0.9 s
# walking the list itself). Walk the list in the recursion, or materialize
# what the loop needs in one pass. A literal index (`List.get(.., xs, 0n)`)
# is a head access and exempt, as are laws and proofs.
import Base
import ../../src.bend as Src
import ../../finding.bend as F
import ../../../syntax/lex.bend as Lex
import ../../../syntax/tree.bend as Tree
import ../calls.bend as Calls

# is the chain exactly one number?
def literal(n: Tree.Node) -> Bool:
  match n:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TNum{}, t, l, c}}, Tree.NNil{}}:
      True{}
    case other:
      False{}

# every List.get / String.get call at a computed index
def walk(n: Tree.Node, +path: String) -> List<&2, F.Finding>:
  match n:
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, +t, +l, +c}}, Tree.NCons{Tree.Group{Lex.Tok{_, +o, _, _}, +kids, _}, rest}}:
      +list = String.eq(t, "List.get")
      +get = Bool.and(String.eq(o, "("), Bool.or(list, String.eq(t, "String.get")))
      +fire = Bool.and(get, Bool.not(literal(Calls.arg(Calls.args(kids), Bool.pick(Nat, list, 3n, 1n)))))
      +more = List.concat(&2, F.Finding, [walk(kids, path), walk(rest, path)])
      Bool.pick(List<&2, F.Finding>, fire,
        F.Finding{path, l, c, U32.from_nat(String.length(t)), "index",
          t ++ " inside a recursive def walks the list each step: quadratic; walk the list itself"} <> more,
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
        Bool.pick(List<&2, F.Finding>, Bool.and(Calls.calls(body, name), Bool.not(Calls.exempt(path, sig))),
          walk(body, path), []) <> acc)

# the rule
def check(s: Src.Src) -> List<&2, F.Finding>:
  Src.Src{path, text, toks, tree, bound, items} = s
  check.go(Calls.defs(tree), path, [])
