# rule pick: a def calls itself in a branch of a `Bool.pick`. Bool.pick is a
# function, so both branches are evaluated whatever the condition. In both
# branches, two recursive calls a step is 2^n work where one was meant (a
# per-token scan that took 20 s this way took 20 ms as one pass): bind the
# call once above the pick (`+more = go(rest)`) and pick between `x <> more`
# and `more`. In one branch, the recursion runs even when the other branch
# was the answer: a search never stops early and walks the whole input
# (portal-bend's `get`, bendoom's sorted insert). Match on the Bool instead,
# in a helper that takes it as a parameter. A pick nested in a branch of one
# already reported is not reported again.
import Base
import ../../src.bend as Src
import ../../finding.bend as F
import ../../../syntax/lex.bend as Lex
import ../../../syntax/tree.bend as Tree
import ../calls.bend as Calls

# do both branches (the third and fourth arguments) name the def?
def both(+as: List<&2, Tree.Node>, +name: String) -> Bool:
  Bool.and(Calls.mentions(Calls.arg(as, 2n), name), Calls.mentions(Calls.arg(as, 3n), name))

# does either branch call the def?
def once(+as: List<&2, Tree.Node>, +name: String) -> Bool:
  Bool.or(Calls.calls(Calls.arg(as, 2n), name), Calls.calls(Calls.arg(as, 3n), name))

# every `Bool.pick(..)` in a chain, at any depth, that recurses in both
# branches or in one; quiet: inside a branch of a reported pick
def picks(n: Tree.Node, +name: String, +path: String, +quiet: Bool) -> List<&2, F.Finding>:
  match n:
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, +t, +l, +c}}, Tree.NCons{Tree.Group{open, +kids, close}, rest}}:
      +as = Calls.args(kids)
      +ispick = String.eq(t, "Bool.pick")
      +two = Bool.and(ispick, both(as, name))
      +one = Bool.and(Bool.and(ispick, Bool.not(two)), Bool.and(Bool.not(quiet), once(as, name)))
      +more = List.concat(&2, F.Finding, [picks(kids, name, path, Bool.or(quiet, Bool.or(two, one))),
        picks(rest, name, path, quiet)])
      Bool.pick(List<&2, F.Finding>, two,
        F.Finding{path, l, c, 9, "pick", name ++ " recurses in both branches; Bool.pick runs both"} <> more,
        Bool.pick(List<&2, F.Finding>, one,
          F.Finding{path, l, c, 9, "pick",
            name ++ " recurses in one branch; Bool.pick runs it whatever the condition (no early exit)"} <> more,
          more))
    case Tree.NCons{Tree.Group{open, kids, close}, rest}:
      List.concat(&2, F.Finding, [picks(kids, name, path, quiet), picks(rest, name, path, quiet)])
    case Tree.NCons{Tree.Stmt{kind, kids, body}, rest}:
      List.concat(&2, F.Finding, [picks(kids, name, path, quiet), picks(body, name, path, quiet),
        picks(rest, name, path, quiet)])
    case Tree.NCons{h, rest}:
      picks(rest, name, path, quiet)
    case other:
      Nil{}

def check.go(ds: List<&2, Calls.Def>, +path: String, acc: List<&2, List<&2, F.Finding>>) -> List<&2, F.Finding>:
  match ds:
    case Nil{}:
      List.concat(&2, F.Finding, List.reverse(&2, List<&2, F.Finding>, acc))
    case Con{Calls.Def{+name, sig, body}, rest}:
      check.go(rest, path, picks(body, name, path, False{}) <> acc)

# the rule
def check(s: Src.Src) -> List<&2, F.Finding>:
  Src.Src{path, text, toks, tree, bound, items} = s
  check.go(Calls.defs(tree), path, [])
