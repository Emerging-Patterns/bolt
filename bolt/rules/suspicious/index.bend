# rule index: a def that calls itself also calls `List.get(..)` or
# `String.get(..)`. Both walk the cons list from the head to the index, so a
# per-index loop is quadratic (AppSprout's sort went from 39 s to 0.9 s
# walking the list itself). Walk the list in the recursion, or materialize
# what the loop needs in one pass. A get anywhere in the def is reported,
# one in a base arm that runs once included. A literal index of any size
# (`List.get(.., xs, 0n)`, `5000n`) is exempt, as are laws and proofs. A
# `List.get` on a fixed table (a literal, a sized array, a constant
# `List.replicate`) is `table`'s finding instead, so the two rules do not
# both report that call. `String.get` is never `table`'s: it stays here.
import Base
import ../../src.bend as Src
import ../../finding.bend as F
import ../../../syntax/lex.bend as Lex
import ../../../syntax/tree.bend as Tree
import ../calls.bend as Calls
import ../../../lazy/lazy.bend as Lazy
import ./table.bend as Table

# is the chain exactly one number?
def literal(nn: Tree.Node) -> Bool:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TNum{}, t, l, c}}, Tree.NNil{}}:
      True{}
    case other:
      False{}

# a fixed table is reported by `table`, not here
def held(+list: Bool, coll: Tree.Node, +fixed: List<&2, String>) -> Bool:
  match list:
    case False{}:
      False{}
    case True{}:
      Table.owns(coll, fixed)

# every List.get / String.get call at a computed index
def walk(nn: Tree.Node, +path: String, +fixed: List<&2, String>) -> List<&2, F.Finding>:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, +t, +l, +c}}, Tree.NCons{Tree.Group{Lex.Tok{_, +o, _, _}, +kids, _}, rest}}:
      +list = String.eq(t, "List.get")
      +as = Calls.args(kids)
      +get = Bool.and(String.eq(o, "("), Bool.or(list, String.eq(t, "String.get")))
      +fire = Bool.and(get, Bool.and(Bool.not(literal(Calls.arg(as, Bool.pick(Nat, list, 3n, 1n)))),
        Bool.not(held(list, Calls.arg(as, 2n), fixed))))
      +more = List.concat(&2, F.Finding, [walk(kids, path, fixed), walk(rest, path, fixed)])
      Bool.pick(List<&2, F.Finding>, fire,
        F.Finding{path, l, c, U32.from_nat(String.length(t)), "index",
          t ++ " inside a recursive def walks the list again on each step, which is quadratic; walk the list itself."} <> more,
        more)
    case Tree.NCons{Tree.Group{open, +kids, close}, rest}:
      List.concat(&2, F.Finding, [walk(kids, path, fixed), walk(rest, path, fixed)])
    case Tree.NCons{Tree.Stmt{kind, +kids, body}, rest}:
      List.concat(&2, F.Finding, [walk(kids, path, fixed), walk(body, path, fixed), walk(rest, path, fixed)])
    case Tree.NCons{h, rest}:
      walk(rest, path, fixed)
    case other:
      Nil{}

def check.go(
  ds: List<&2, Calls.Def>,
  +mods: List<&2, String>,
  +path: String,
  acc: List<&2, List<&2, F.Finding>>
) -> List<&2, F.Finding>:
  match ds:
    case Nil{}:
      List.concat(&2, F.Finding, List.reverse(&2, List<&2, F.Finding>, acc))
    case Con{Calls.Def{+name, +sig, +body}, rest}:
      check.go(rest, mods, path,
        Lazy.stop(List<&2, F.Finding>,
          Bool.not(Bool.and(Calls.calls(body, name), Bool.not(Calls.exempt(path, sig)))), [],
          _u => walk(body, path, Table.scope(body, mods))) <> acc)

# the rule
def check(ss: Src.Src) -> List<&2, F.Finding>:
  Src.Src{path, text, toks, tree, bound, items} = ss
  +ds = Calls.defs(tree)
  check.go(ds, Table.modules(ds, []), path, [])
