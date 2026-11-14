# a chain of the tree as law vocabulary: what it starts with, and what comes
# after its first node. bolt never calls any of it
import Base
import ../../src/syntax/lex.bend as Lex
import ../../src/syntax/tree.bend as Tree
import ./TokenKinds.bend as D1

# what a chain starts with: a leaf of some kind, a group, or neither
type Front is Data:
  FLeaf{kind: Lex.TokKind}
  FGroup{}
  FOther{}

# what a chain starts with
def chains.front(rest: Tree.Node) -> Front:
  match rest:
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, _t, _l, _c}}, _r}:
      FLeaf{k}
    case Tree.NCons{Tree.Group{_o, _g, _cl}, _r}:
      FGroup{}
    case _other:
      FOther{}

# a chain after its first node; nothing after a chain that has none
def chains.after(rest: Tree.Node) -> Tree.Node:
  match rest:
    case Tree.NCons{_h, r}:
      r
    case _other:
      Tree.NNil{}

# is it a leaf of one of these kinds?
def chains.leaf_of(f: Front, ks: List<&2, Lex.TokKind>) -> Bool:
  match f:
    case FLeaf{k}:
      D1.kinds.among(k, ks)
    case _other:
      False{}

# is it a group?
def chains.is_group(f: Front) -> Bool:
  match f:
    case FGroup{}:
      True{}
    case _other:
      False{}

# is the chain a node and the rest of a chain?
def chains.is_cons(n: Tree.Node) -> Bool:
  match n:
    case Tree.NCons{_h, _r}:
      True{}
    case _other:
      False{}

# is a node a leaf of one of these kinds?
def chains.node_of(n: Tree.Node, ks: List<&2, Lex.TokKind>) -> Bool:
  match n:
    case Tree.Leaf{Lex.Tok{k, _t, _l, _c}}:
      D1.kinds.among(k, ks)
    case _other:
      False{}
