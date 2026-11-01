# `twice` reports exactly, in a def that calls itself, a list pattern in a
# case's first match column opening with the same literal twice.
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/syntax/bind.bend as Bind
import ../src/src.bend as Src
import ../src/syntax/tree.bend as Tree
import ../src/syntax/outline.bend as Outline
import ../src/rules/calls.bend as Calls
import ../src/rules/tokens.bend as T
import ../src/rules/correctness/twice.bend as Twice

# the text of the literal a list pattern opens with: `x <> ..` or `Con{x, ..}`
def twice.first(pat: Tree.Node) -> Maybe<&2, String>:
  match pat:
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}}, Tree.NCons{Tree.Leaf{Lex.Tok{k2, +o, l2, c2}}, rest}}:
      Bool.pick(Maybe<&2, String>, Bool.and(T.is_lit(k), String.eq(o, "<>")), Some{t}, None{})
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TUpper{}, +t, l, c}},
        Tree.NCons{Tree.Group{open, Tree.NCons{Tree.Leaf{Lex.Tok{k, x, l2, c2}}, kids}, close}, rest}}:
      Bool.pick(Maybe<&2, String>, Bool.and(String.eq(t, "Con"), T.is_lit(k)), Some{x}, None{})
    case other:
      None{}

# a list pattern past its first element: past `x <>`, or past `Con{x,`
def twice.after(pat: Tree.Node) -> Tree.Node:
  match pat:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TUpper{}, t, l, c}},
        Tree.NCons{Tree.Group{open, Tree.NCons{x, Tree.NCons{comma, kids}}, close}, rest}}:
      kids
    case Tree.NCons{x, Tree.NCons{op, rest}}:
      rest
    case other:
      Tree.NNil{}

# two literals, both there and the same text
def twice.same(aa: Maybe<&2, String>, bb: Maybe<&2, String>) -> Bool:
  match aa bb:
    case Some{x} Some{y}:
      String.eq(x, y)
    case a2 b2:
      False{}

# a list pattern that opens with the same literal twice
def twice.dup(+pat: Tree.Node) -> Bool:
  twice.same(twice.first(pat), twice.first(twice.after(pat)))

# how many case statements under the node, at any depth, hold a pattern that
# opens with the same literal twice
def twice.cases(nn: Tree.Node) -> Nat:
  match nn:
    case Tree.NCons{Tree.Stmt{Tree.SCase{}, kids, body}, rest}:
      Nat.add(Bool.pick(Nat, twice.dup(T.pattern(kids)), 1n, 0n), Nat.add(twice.cases(body), twice.cases(rest)))
    case Tree.NCons{Tree.Stmt{kind, kids, body}, rest}:
      Nat.add(twice.cases(body), twice.cases(rest))
    case Tree.NCons{h, rest}:
      twice.cases(rest)
    case other:
      0n

# a def's such case statements, when its body calls it, `name(..)`
def twice.def(mm: Maybe<&2, String>, +body: Tree.Node) -> Nat:
  match mm:
    case None{}:
      0n
    case Some{+name}:
      Bool.pick(Nat, Calls.calls(body, name), twice.cases(body), 0n)

# how many such case statements the top-level defs that call themselves hold
def twice_count(root: Tree.Node) -> Nat:
  match root:
    case Tree.NCons{Tree.Stmt{Tree.SDef{}, kids, body}, rest}:
      Nat.add(twice.def(Bind.declared(kids), body), twice_count(rest))
    case Tree.NCons{h, rest}:
      twice_count(rest)
    case other:
      0n

# LAW: twice reports one finding for each case statement, at any depth under
# a top-level def whose body calls the def, whose pattern (read from its first
# column) opens with the same literal twice, and none for any other
law twice_counts:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for +tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Twice.check(Src.Src{path, text, toks, tree, bound, items})) == twice_count(tree) : Nat}
