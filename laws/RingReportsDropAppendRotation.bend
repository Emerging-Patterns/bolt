# `ring` reports exactly, in a def that calls itself, a self-call argument
# that appends onto a drop by a number literal, or a tail, of the parameter in
# its own position, when no `match` of the def has that parameter as a
# scrutinee.
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/syntax/bind.bend as Bind
import ../src/src.bend as Src
import ../src/syntax/tree.bend as Tree
import ../src/syntax/outline.bend as Outline
import ../src/rules/suspicious/ring.bend as Ring
import ../src/rules/calls.bend as Calls

# ring: one when the scan found a drop, else zero
def ring.hit(mm: Maybe<&2, Lex.Tok>) -> Nat:
  match mm:
    case None{}:
      0n
    case Some{t}:
      1n

# how many self-call arguments slide the window of their own slot: argument
# i is read against parameter i only (Ring.slot_wins: that parameter, when
# it is a window), and slides when Ring.plus_scan finds, over it, a
# `List.drop` / `String.drop` of the window by a number literal or a
# `List.tail` / `String.tail` of it, that is then `++`-appended onto or is
# the receiver of `List.append` / `String.append`. What is appended is not
# measured: the drop is the fixed part.
def ring.args(as: List<&2, Tree.Node>, +params: List<&2, String>, +wins: List<&2, String>) -> Nat:
  match as:
    case Nil{}:
      0n
    case Con{h, rest}:
      +slot = Maybe.default(&2, String, List.head(&2, String, params), "")
      Nat.add(ring.hit(Ring.plus_scan(h, None{}, Ring.slot_wins(slot, wins))),
        ring.args(rest, List.tail(&2, String, params), wins))

# how many sliding arguments the self-calls `self(..)` under the node hold,
# at any depth
def ring.count(nn: Tree.Node, +self: String, +params: List<&2, String>, +wins: List<&2, String>) -> Nat:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, +t, l, c}}, Tree.NCons{Tree.Group{Lex.Tok{_k, +o, _l, _c}, +kids, _e}, rest}}:
      Nat.add(Bool.pick(Nat, Bool.and(String.eq(o, "("), String.eq(t, self)), ring.args(Calls.args(kids), params, wins),
        0n), Nat.add(ring.count(kids, self, params, wins), ring.count(rest, self, params, wins)))
    case Tree.NCons{Tree.Group{open, kids, close}, rest}:
      Nat.add(ring.count(kids, self, params, wins), ring.count(rest, self, params, wins))
    case Tree.NCons{Tree.Stmt{kind, kids, body}, rest}:
      Nat.add(ring.count(kids, self, params, wins),
        Nat.add(ring.count(body, self, params, wins), ring.count(rest, self, params, wins)))
    case Tree.NCons{h, rest}:
      ring.count(rest, self, params, wins)
    case other:
      0n

# LAW: over any chain, ring reports one finding for each argument of a
# self-call that drops and appends the window in its own parameter slot, and
# none for a window moved to another parameter's slot or any other call
law ring_walk_counts:
  for nn: Tree.Node
  for +self: String
  for +params: List<&2, String>
  for +path: String
  for +wins: List<&2, String>
  {List.length(&2, F.Finding, Ring.walk(nn, self, params, path, wins)) == ring.count(nn, self, params, wins) : Nat}

# the sliding arguments of each def of the list that calls itself and is not
# exempt; its windows are its parameters not named as any scrutinee of a
# `match` in its body (Ring.windows)
def ring.defs(ds: List<&2, Calls.Def>, +path: String) -> Nat:
  match ds:
    case Nil{}:
      0n
    case Con{Calls.Def{+name, +sig, +body}, rest}:
      Nat.add(Bool.pick(Nat, Bool.and(Calls.calls(body, name), Bool.not(Calls.exempt(path, sig))),
        ring.count(body, name, Calls.names(sig), Ring.windows(sig, body)), 0n), ring.defs(rest, path))

# LAW: ring reports exactly those arguments, def by def, over the defs of the
# tree that call themselves, and none in a def that does not
law ring_counts:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Ring.check(Src.Src{path, text, toks, tree, bound, items}))
    == ring.defs(Calls.defs(tree), path) : Nat}
