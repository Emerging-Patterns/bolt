# `closed` reports any law in a LAWS.bend with no binder.
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/syntax/bind.bend as Bind
import ../src/paths.bend as Paths
import ../src/src.bend as Src
import ../src/syntax/tree.bend as Tree
import ../src/syntax/outline.bend as Outline
import ../src/rules/laws/closed.bend as Closed

# closed (laws/ClosedReportsBinderlessLaws.bend). Over the file's top-level statements the rule reports
# each law whose body holds no `for` or `exs` line (the tree's SFor
# statement), and it reads only a LAWS.bend.

# some statement of a law's body is a `for` or `exs` binder
def closed.bound(body: Tree.Node) -> Bool:
  match body:
    case Tree.NCons{Tree.Stmt{Tree.SFor{}, kids, b}, rest}:
      True{}
    case Tree.NCons{h, rest}:
      closed.bound(rest)
    case other:
      False{}

# how many of the top-level laws bind nothing
def closed.count(root: Tree.Node) -> Nat:
  match root:
    case Tree.NCons{Tree.Stmt{Tree.SLaw{}, kids, +body}, rest}:
      +m = closed.count(rest)
      Bool.pick(Nat, closed.bound(body), m, 1n+m)
    case Tree.NCons{h, rest}:
      closed.count(rest)
    case other:
      0n

# LAW: over the file's top-level statements, closed reports one finding for
# each law with no `for` or `exs` binder, equality or not, and none for any
# other statement
law closed_walk_counts:
  for root: Tree.Node
  for +path: String
  {List.length(&2, F.Finding, Closed.check.go(root, path)) == closed.count(root) : Nat}

# LAW: closed reports exactly those laws of a LAWS.bend, and nothing in any
# other file, whatever the source holds
law closed_counts:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for +tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Closed.check(Src.Src{path, text, toks, tree, bound, items}))
    == Bool.pick(Nat, Paths.is_laws(path), closed.count(tree), 0n) : Nat}
