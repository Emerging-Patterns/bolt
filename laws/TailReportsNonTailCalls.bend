# `tail` reports exactly a non-tail self-call outside any `Bool.pick(..)` in a
# def whose first live parameter's type is a List or String, whether or not
# the call shrinks it.
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/syntax/bind.bend as Bind
import ../src/src.bend as Src
import ../src/syntax/tree.bend as Tree
import ../src/syntax/outline.bend as Outline
import ../src/rules/pedantic/tail.bend as Tail
import ../src/rules/calls.bend as Calls

# tail (laws/TailReportsNonTailCalls.bend). Over a def's statements the rule reports each call
# `name(..)` of the def itself, except inside a `Bool.pick(..)` and except
# when the call is a statement's whole chain (a tail call); over the file it
# does that for each def whose first live parameter is a List or a String
# (Calls.seq) and that is not exempt (a law file, or a def returning a
# proof), the call shrinking that parameter or not.

# a statement's chain is exactly a call of the name, `name(..)`, and nothing more
def tail.whole(kids: Tree.Node, +name: String) -> Bool:
  match kids:
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, +t, l, c}}, Tree.NCons{Tree.Group{Lex.Tok{j, +o, m, n}, g, e}, Tree.NNil{}}}:
      Bool.and(String.eq(t, name), String.eq(o, "("))
    case other:
      False{}

# how many self-calls of the name sit under the node: outside any
# `Bool.pick(..)`, and not counting the chain's head call when whole says the
# chain is a statement's whole chain
def tail.count(nn: Tree.Node, +name: String, whole: Bool) -> Nat:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, +t, l, c}}, Tree.NCons{Tree.Group{Lex.Tok{_k, +o, _l, _c}, kids, _e}, rest}}:
      +call = String.eq(o, "(")
      +m = Nat.add(Bool.pick(Nat, Bool.and(call, String.eq(t, "Bool.pick")), 0n, tail.count(kids, name, False{})),
        tail.count(rest, name, False{}))
      Bool.pick(Nat, Bool.and(Bool.and(call, String.eq(t, name)), Bool.not(whole)), 1n+m, m)
    case Tree.NCons{Tree.Group{open, kids, close}, rest}:
      Nat.add(tail.count(kids, name, False{}), tail.count(rest, name, False{}))
    case Tree.NCons{Tree.Stmt{kind, +kids, body}, rest}:
      Nat.add(tail.count(kids, name, tail.whole(kids, name)),
        Nat.add(tail.count(body, name, False{}), tail.count(rest, name, False{})))
    case Tree.NCons{h, rest}:
      tail.count(rest, name, False{})
    case other:
      0n

# how many non-tail self-calls the defs hold, over the defs that walk a List
# or a String and are not exempt
def tail.total(ds: List<&2, Calls.Def>, +path: String) -> Nat:
  match ds:
    case Nil{}:
      0n
    case Con{Calls.Def{+name, +sig, body}, rest}:
      Nat.add(Bool.pick(Nat, Bool.and(Calls.seq(sig), Bool.not(Calls.exempt(path, sig))),
        tail.count(body, name, False{}), 0n), tail.total(rest, path))

# LAW: over a def's statements, tail reports one finding for each self-call
# outside any `Bool.pick(..)` that is not a statement's whole chain, and
# none for anything else
law tail_walk_counts:
  for nn: Tree.Node
  for +name: String
  for +path: String
  for skip: Bool
  {List.length(&2, F.Finding, Tail.walk(nn, name, path, skip)) == tail.count(nn, name, skip) : Nat}

# LAW: tail reports exactly those self-calls of each of the file's defs whose
# first live parameter is a List or a String and that is not exempt, and
# none in any other def
law tail_counts:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Tail.check(Src.Src{path, text, toks, tree, bound, items}))
    == tail.total(Calls.defs(tree), path) : Nat}
