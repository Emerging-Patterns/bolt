# `unit` reports exactly a multiply or divide by one on a recursive step.
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/syntax/bind.bend as Bind
import ../src/src.bend as Src
import ../src/syntax/tree.bend as Tree
import ../src/syntax/outline.bend as Outline
import ../src/rules/suspicious/unit.bend as UnitRule
import ../src/rules/calls.bend as Calls

# unit (laws/UnitReportsMultiplyByOne.bend). The rule walks each def of the file that calls
# itself (Calls.calls) and is not exempt (a law file, a proof file, a def
# returning a proof), its body hot: the recursive step. A case arm's body is
# hot only when it calls the def too (a base case is not), a case's own
# pattern tokens never; anything else, lambda bodies included, is as hot as
# what holds it. In a hot region it reports one finding for each operator
# `*` with the literal one (a number token `1`, `1n` or `1.0`) right after or
# right before it, or `/` with it right after (the divisor); and one for each
# call, a leaf then a `(` group, of `Nat.mul`, `U32.mul` or `F32.mul` with
# the literal one alone as some argument, or of `Nat.div`, `U32.div` or
# `F32.div` with it alone as the last. Right before an operator is the leaf
# just before it in its chain, none past a group, a statement or another
# operator; right after is the node just after it, when a leaf.

# does the maybe hold the literal one: a number token `1`, `1n` or `1.0`?
def unit.one(mm: Maybe<&2, Lex.Tok>) -> Bool:
  match mm:
    case Some{Lex.Tok{Lex.TNum{}, +t, l, c}}:
      Bool.or(String.eq(t, "1"), Bool.or(String.eq(t, "1n"), String.eq(t, "1.0")))
    case other:
      False{}

# is the operator's text `*` with the literal one after or before it, or `/`
# with it after?
def unit.by_one(+op: String, prev: Maybe<&2, Lex.Tok>, +nxt: Maybe<&2, Lex.Tok>) -> Bool:
  Bool.pick(Bool, String.eq(op, "*"), Bool.or(unit.one(nxt), unit.one(prev)),
    Bool.and(String.eq(op, "/"), unit.one(nxt)))

# is the token an operator by one, between prev and nxt?
def unit.hit(tok: Lex.Tok, prev: Maybe<&2, Lex.Tok>, nxt: Maybe<&2, Lex.Tok>) -> Bool:
  match tok:
    case Lex.Tok{Lex.TOp{}, t, l, c}:
      unit.by_one(t, prev, nxt)
    case other:
      False{}

# what an operator after this leaf sees before it: the leaf, none when it is
# an operator
def unit.next(tok: Lex.Tok) -> Maybe<&2, Lex.Tok>:
  match tok:
    case Lex.Tok{Lex.TOp{}, t, l, c}:
      None{}
    case other:
      Some{other}

# the node right after, when it is a leaf
def unit.first(nn: Tree.Node) -> Maybe<&2, Lex.Tok>:
  match nn:
    case Tree.NCons{Tree.Leaf{tok}, rest}:
      Some{tok}
    case other:
      None{}

# the name a group right after the leaf calls, "" after no leaf
def unit.name(mm: Maybe<&2, Lex.Tok>) -> String:
  match mm:
    case None{}:
      ""
    case Some{Lex.Tok{k, t, l, c}}:
      t

# is the argument the literal one alone?
def unit.lone(aa: Tree.Node) -> Bool:
  match aa:
    case Tree.NCons{Tree.Leaf{tok}, Tree.NNil{}}:
      unit.one(Some{tok})
    case other:
      False{}

# is some argument the literal one alone?
def unit.any(as: List<&2, Tree.Node>) -> Bool:
  match as:
    case Nil{}:
      False{}
    case Con{h, rest}:
      Bool.or(unit.lone(h), unit.any(rest))

# is the last argument the literal one alone?
def unit.last(as: List<&2, Tree.Node>) -> Bool:
  match as:
    case Nil{}:
      False{}
    case Con{h, Nil{}}:
      unit.lone(h)
    case Con{h, rest}:
      unit.last(rest)

# is the call a multiply with some argument one, else a divide by one?
def unit.call(+tt: String, +as: List<&2, Tree.Node>) -> Bool:
  Bool.pick(Bool, List.contains(~String, ~String.eq, ["Nat.mul", "U32.mul", "F32.mul"], tt),
    unit.any(as),
    Bool.and(List.contains(~String, ~String.eq, ["Nat.div", "U32.div", "F32.div"], tt),
      unit.last(as)))

# how many multiplies and divides by one the chain holds, at any depth, from
# a region as hot as hot, the leaf before it prev
def unit.count(nn: Tree.Node, +prev: Maybe<&2, Lex.Tok>, +self: String, +hot: Bool) -> Nat:
  match nn:
    case Tree.NCons{Tree.Leaf{+tok}, +rest}:
      +m = unit.count(rest, unit.next(tok), self, hot)
      Bool.pick(Nat, Bool.and(hot, unit.hit(tok, prev, unit.first(rest))), 1n+m, m)
    case Tree.NCons{Tree.Group{Lex.Tok{ok, +o, ol, oc}, +kids, close}, rest}:
      +own = Bool.and(String.eq(o, "("), Bool.and(hot, unit.call(unit.name(prev), Calls.args(kids))))
      Nat.add(unit.count(kids, None{}, self, hot),
        Nat.add(Bool.pick(Nat, own, 1n, 0n), unit.count(rest, None{}, self, hot)))
    case Tree.NCons{Tree.Stmt{Tree.SCase{}, kids, +body}, rest}:
      Nat.add(unit.count(kids, None{}, self, False{}),
        Nat.add(unit.count(body, None{}, self, Bool.and(hot, Calls.calls(body, self))), unit.count(rest, None{}, self,
          hot)))
    case Tree.NCons{Tree.Stmt{kind, kids, body}, rest}:
      Nat.add(unit.count(kids, None{}, self, hot),
        Nat.add(unit.count(body, None{}, self, hot), unit.count(rest, None{}, self, hot)))
    case Tree.NCons{h, rest}:
      unit.count(rest, prev, self, hot)
    case other:
      0n

# LAW: over any chain, unit reports one finding for each multiply or divide
# by one in a hot region, and none for anything else
law unit_walk_counts:
  for nn: Tree.Node
  for +prev: Maybe<&2, Lex.Tok>
  for +self: String
  for +path: String
  for +hot: Bool
  {List.length(&2, F.Finding, UnitRule.walk(nn, prev, self, path, hot)) == unit.count(nn, prev, self, hot) : Nat}

# the multiplies and divides by one of each def of the list that calls itself
# and is not exempt, its body hot
def unit.defs(ds: List<&2, Calls.Def>, +path: String) -> Nat:
  match ds:
    case Nil{}:
      0n
    case Con{Calls.Def{+name, +sig, +body}, rest}:
      Nat.add(Bool.pick(Nat, Bool.and(Calls.calls(body, name), Bool.not(Calls.exempt(path, sig))),
        unit.count(body, None{}, name, True{}), 0n), unit.defs(rest, path))

# LAW: unit reports exactly those, def by def, over the defs of the tree
law unit_counts:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, UnitRule.check(Src.Src{path, text, toks, tree, bound, items}))
    == unit.defs(Calls.defs(tree), path) : Nat}
