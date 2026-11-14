# `pick` reports exactly a self-call in one or both branches of `Bool.pick`,
# and does not report again a nested pick in a branch it reported.
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/syntax/bind.bend as Bind
import ../src/src.bend as Src
import ../src/syntax/tree.bend as Tree
import ../src/syntax/outline.bend as Outline
import ../src/rules/correctness/pick.bend as Pick
import ../src/rules/calls.bend as Calls
import ../src/rules/tokens.bend as T

# The eager Bool combinators: pick (laws/PickReportsSelfCalls.bend) and strict
# (laws/StrictReportsEagerSelfCalls.bend). Both walk each def's body in the tree and look for a
# self-call, the def's own name followed by a `(` group (Calls.calls),
# counted here over every chain the walk can meet.

# does a branch of a pick, its third or fourth argument, call the def?
def pick.branch(+as: List<&2, Tree.Node>, +name: String) -> Bool:
  Bool.or(Calls.calls(Calls.arg(as, 2n), name), Calls.calls(Calls.arg(as, 3n), name))

# is argument nth of `Bool.pick(T, c, a, b)` a branch: a or b?
def pick.branch_arg(nth: Nat) -> Bool:
  match nth:
    case 2n:
      True{}
    case 3n:
      True{}
    case other:
      False{}

# is the token a top-level comma, which starts the next argument?
def pick.comma(k: Lex.TokKind) -> Bool:
  match k:
    case Lex.TComma{}:
      True{}
    case other:
      False{}

# the argument after a token: one further past a comma
def pick.step(k: Lex.TokKind, +nth: Nat) -> Nat:
  Bool.pick(Nat, pick.comma(k), 1n+nth, nth)

# argument nth of a group is quiet when the group is (quiet), or when it is
# a branch of a pick counted (hush)
def pick.hushed(+quiet: Bool, +hush: Bool, nth: Nat) -> Bool:
  Bool.or(quiet, Bool.and(hush, pick.branch_arg(nth)))

# how many `Bool.pick` calls in the chain, at any depth, call the def in a
# branch and are not quiet: a pick in a branch of a pick counted is not
# counted again, one in its condition is. The chain is argument nth of a
# group with quiet and hush
def pick.count(nn: Tree.Node, +name: String, +quiet: Bool, +hush: Bool, +nth: Nat) -> Nat:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}}, Tree.NCons{Tree.Group{open, +kids, close}, rest}}:
      +at = pick.step(k, nth)
      +q = pick.hushed(quiet, hush, at)
      +hit = Bool.and(String.eq(t, "Bool.pick"), Bool.and(Bool.not(q), pick.branch(Calls.args(kids), name)))
      +m = Nat.add(pick.count(kids, name, q, hit, 0n), pick.count(rest, name, quiet, hush, at))
      Bool.pick(Nat, hit, 1n+m, m)
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}}, rest}:
      pick.count(rest, name, quiet, hush, pick.step(k, nth))
    case Tree.NCons{Tree.Group{open, kids, close}, rest}:
      Nat.add(pick.count(kids, name, pick.hushed(quiet, hush, nth), False{}, 0n), pick.count(rest, name, quiet, hush,
        nth))
    case Tree.NCons{Tree.Stmt{kind, kids, body}, rest}:
      Nat.add(pick.count(kids, name, pick.hushed(quiet, hush, nth), False{}, 0n),
        Nat.add(pick.count(body, name, pick.hushed(quiet, hush, nth), False{}, 0n), pick.count(rest, name, quiet, hush,
          nth)))
    case Tree.NCons{h, rest}:
      pick.count(rest, name, quiet, hush, nth)
    case other:
      0n

# LAW: the rule's quiet for argument nth of a group is the law's: the
# group's quiet, hushed too in a branch (the third or fourth argument)
law pick_mute:
  for +quiet: Bool
  for +hush: Bool
  for nth: Nat
  {Pick.mute(quiet, hush, nth) == pick.hushed(quiet, hush, nth) : Bool}

# LAW: the rule moves to the next argument exactly past a comma
law pick_next:
  for k: Lex.TokKind
  for +nth: Nat
  {Pick.next(k, nth) == pick.step(k, nth) : Nat}

# LAW: over any chain, pick reports one finding for each `Bool.pick(..)` whose
# third or fourth argument calls the def, in both or in one, none for a pick
# inside a branch of one it reported, and one for a pick in its condition
law pick_walk_counts:
  for n: Tree.Node
  for +name: String
  for +path: String
  for +quiet: Bool
  for +hush: Bool
  for +nth: Nat
  {List.length(&2, F.Finding, Pick.walk(n, name, path, quiet, hush, nth))
    == pick.count(n, name, quiet, hush, nth) : Nat}

# LAW: a def's body is walked outside any pick's arguments
law pick_picks_counts:
  for nn: Tree.Node
  for +name: String
  for +path: String
  for +quiet: Bool
  {List.length(&2, F.Finding, Pick.picks(nn, name, path, quiet)) == pick.count(nn, name, quiet, False{}, 0n) : Nat}

# the picks of each def of the list, none in an exempt one (a law file, a
# proof file, a def that returns a proof)
def pick.defs(ds: List<&2, Calls.Def>, +path: String) -> Nat:
  match ds:
    case Nil{}:
      0n
    case Con{Calls.Def{+name, +sig, body}, rest}:
      Nat.add(Bool.pick(Nat, Calls.exempt(path, sig), 0n, pick.count(body, name, False{}, False{}, 0n)),
        pick.defs(rest, path))

# LAW: pick reports exactly those picks, def by def, over the defs of the tree
law pick_counts:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Pick.check(Src.Src{path, text, toks, tree, bound, items}))
    == pick.defs(Calls.defs(tree), path) : Nat}
