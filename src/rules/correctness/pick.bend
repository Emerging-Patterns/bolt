# rule pick: a def calls itself in a branch of a `Bool.pick`. Bool.pick is a
# function, so both branches are evaluated whatever the condition. In both
# branches, two recursive calls a step is 2^n work where one was meant (a
# per-token scan that took 20 s this way took 20 ms as one pass): bind the
# call once above the pick (`+more = go(rest)`) and pick between `x <> more`
# and `more`. In one branch, the recursion runs even when the other branch
# was the answer: a search never stops early and walks the whole input
# (portal-bend's `get`, bendoom's sorted insert). Match on the Bool instead,
# in a helper that takes it as a parameter. A self-call is the def's name
# followed by `(..)`: a parameter or a value named like the def is not one. A
# pick nested in a branch of one already reported is not reported again; one
# nested in its condition is. A
# law file, a proof file and a def that is a proof never run, so they are
# exempt: a def that returns a proof, or one written with no type at all
# (`def f(x, y):`), which fills the law named f.
import Base
import ../../src.bend as Src
import ../../finding.bend as F
import ../../syntax/lex.bend as Lex
import ../../syntax/tree.bend as Tree
import ../calls.bend as Calls
import ../../lazy/lazy.bend as Lazy

# do both branches (the third and fourth arguments) call the def?
def both(+as: List<&2, Tree.Node>, +name: String) -> Bool:
  Bool.and(Calls.calls(Calls.arg(as, 2n), name), Calls.calls(Calls.arg(as, 3n), name))

# does either branch call the def?
def once(+as: List<&2, Tree.Node>, +name: String) -> Bool:
  Bool.or(Calls.calls(Calls.arg(as, 2n), name), Calls.calls(Calls.arg(as, 3n), name))

# is argument nth of a group quiet: the group's own quiet, or, in a branch
# (the third or fourth argument) of a reported pick, hushed
def mute(+quiet: Bool, +hush: Bool, nth: Nat) -> Bool:
  match nth:
    case 0n:
      quiet
    case 1n:
      quiet
    case 2n:
      Bool.or(quiet, hush)
    case 3n:
      Bool.or(quiet, hush)
    case 4n+p:
      quiet

# the argument a token leaves the walk in: one further past a top-level comma
def next(kk: Lex.TokKind, nth: Nat) -> Nat:
  match kk:
    case Lex.TComma{}:
      1n+nth
    case other:
      nth

# every `Bool.pick(..)` in a chain, at any depth, that recurses in both
# branches or in one. The chain is argument nth of a group with quiet
# (inside a branch of a reported pick) and hush (the group is a reported
# pick, so its branches are quiet); a pick in the condition still counts.
def walk(nn: Tree.Node, +name: String, +path: String, +quiet: Bool, +hush: Bool, +nth: Nat) -> List<&2, F.Finding>:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, +t, +l, +c}}, Tree.NCons{Tree.Group{open, +kids, close}, rest}}:
      +at = next(k, nth)
      +q = mute(quiet, hush, at)
      +as = Calls.args(kids)
      +ispick = String.eq(t, "Bool.pick")
      +two = Bool.and(Bool.and(ispick, Bool.not(q)), both(as, name))
      +one = Bool.and(Bool.and(ispick, Bool.not(two)), Bool.and(Bool.not(q), once(as, name)))
      +more = List.concat(&2, F.Finding, [walk(kids, name, path, q, Bool.or(two, one), 0n),
        walk(rest, name, path, quiet, hush, at)])
      Bool.pick(List<&2, F.Finding>, two,
        F.Finding{path, l, c, 9, "pick",
          name ++ " calls itself in both branches of Bool.pick, which evaluates both, so both calls run; bind the call once above the pick."}
          <> more,
        Bool.pick(List<&2, F.Finding>, one,
          F.Finding{path, l, c, 9, "pick",
            name ++ " calls itself in one branch of Bool.pick, which evaluates both, so the call always runs and never exits early; branch with `match` on the condition instead."}
            <> more,
          more))
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}}, rest}:
      walk(rest, name, path, quiet, hush, next(k, nth))
    case Tree.NCons{Tree.Group{open, kids, close}, rest}:
      List.concat(&2, F.Finding, [walk(kids, name, path, mute(quiet, hush, nth), False{}, 0n),
        walk(rest, name, path, quiet, hush, nth)])
    case Tree.NCons{Tree.Stmt{kind, kids, body}, rest}:
      List.concat(&2, F.Finding, [walk(kids, name, path, mute(quiet, hush, nth), False{}, 0n),
        walk(body, name, path, mute(quiet, hush, nth), False{}, 0n), walk(rest, name, path, quiet, hush, nth)])
    case Tree.NCons{h, rest}:
      walk(rest, name, path, quiet, hush, nth)
    case other:
      Nil{}

# every reported pick in a chain walked at quiet, outside any pick's arguments
def picks(nn: Tree.Node, +name: String, +path: String, +quiet: Bool) -> List<&2, F.Finding>:
  walk(nn, name, path, quiet, False{}, 0n)

def check.go(ds: List<&2, Calls.Def>, +path: String, acc: List<&2, List<&2, F.Finding>>) -> List<&2, F.Finding>:
  match ds:
    case Nil{}:
      List.concat(&2, F.Finding, List.reverse(&2, List<&2, F.Finding>, acc))
    case Con{Calls.Def{+name, +sig, body}, rest}:
      check.go(rest, path,
        Lazy.stop(List<&2, F.Finding>, Calls.exempt(path, sig), [],
          _u => picks(body, name, path, False{})) <> acc)

# the rule
def check(ss: Src.Src) -> List<&2, F.Finding>:
  Src.Src{path, text, toks, tree, bound, items} = ss
  check.go(Calls.defs(tree), path, [])
