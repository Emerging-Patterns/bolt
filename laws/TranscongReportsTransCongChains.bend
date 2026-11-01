# `transcong` (opt-in) reports exactly, in any file (a LAWS.bend and a
# PROOF.bend included), one finding, on the leaf, for each leaf of a name kind
# whose text is `Equal.trans` followed next in its chain by a group opened by
# `(` whose kids hold five comma leaves among their own nodes (six arguments)
# and whose fifth or sixth argument is exactly a leaf of a name kind whose
# text is `Equal.cong` and a group opened by `(` (the kids end right after the
# group or go on with a comma), such leaves found at any depth, under
# statements and inside groups, except among the own nodes of a let statement
# and after a `=` or `<-` leaf earlier in the leaf's own chain (a let the tree
# keeps inside a group); and nothing else.
#
# also rests on: laws/InertTranscong.bend
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/syntax/bind.bend as Bind
import ../src/src.bend as Src
import ../src/syntax/tree.bend as Tree
import ../src/syntax/outline.bend as Outline
import ../src/rules/style/transcong.bend as Transcong

# transcong (laws/TranscongReportsTransCongChains.bend). A site is a name leaf spelling `Equal.trans`,
# then a group opened by `(` whose kids hold five comma leaves of their own
# (six arguments), the fifth or sixth of which opens with a name leaf
# spelling `Equal.cong` and a `(` group and ends right after it (the kids end
# or go on with a comma). Sites are counted at any depth, except among the
# own nodes of a let statement and after a `=` or `<-` leaf in the chain.

# is the node a name leaf spelling the text?
def transcong.name(nn: Tree.Node, +tt: String) -> Bool:
  match nn:
    case Tree.Leaf{Lex.Tok{k, t, l, c}}:
      Bool.and(Lex.is_name(k), String.eq(t, tt))
    case other:
      False{}

# is the node a group opened by `(`?
def transcong.open(nn: Tree.Node) -> Bool:
  match nn:
    case Tree.Group{Lex.Tok{k, o, l, c}, kids, cl}:
      String.eq(o, "(")
    case other:
      False{}

# is the node a comma leaf?
def transcong.comma(nn: Tree.Node) -> Bool:
  match nn:
    case Tree.Leaf{Lex.Tok{k, t, l, c}}:
      Lex.is_comma(k)
    case other:
      False{}

# is the chain over, or does it go on with a comma?
def transcong.last(nn: Tree.Node) -> Bool:
  match nn:
    case Tree.NCons{h, t}:
      transcong.comma(h)
    case other:
      True{}

# a `(` group, then the argument's end
def transcong.call(nn: Tree.Node) -> Bool:
  match nn:
    case Tree.NCons{g, after}:
      Bool.and(transcong.open(g), transcong.last(after))
    case other:
      False{}

# does the chain open an argument that is exactly an `Equal.cong` call?
def transcong.cong(nn: Tree.Node) -> Bool:
  match nn:
    case Tree.NCons{h, t}:
      Bool.and(transcong.name(h, "Equal.cong"), transcong.call(t))
    case other:
      False{}

# how many comma leaves the chain holds among its own nodes
def transcong.commas(nn: Tree.Node) -> Nat:
  match nn:
    case Tree.NCons{h, t}:
      Nat.add(Bool.pick(Nat, transcong.comma(h), 1n, 0n), transcong.commas(t))
    case other:
      0n

# does an argument the fifth or the sixth, from here on, open with an
# `Equal.cong` call? nc: commas so far; fresh: one opens here; seen: one did
def transcong.fed(nn: Tree.Node, +nc: Nat, +fresh: Bool, +seen: Bool) -> Bool:
  match nn:
    case Tree.NCons{+h, +t}:
      transcong.fed(t, Nat.add(nc, Bool.pick(Nat, transcong.comma(h), 1n, 0n)), transcong.comma(h),
        Bool.or(seen, Bool.and(fresh, Bool.and(Bool.or(Nat.is_eq(nc, 4n), Nat.is_eq(nc, 5n)),
          transcong.cong(Tree.NCons{h, t})))))
    case other:
      seen

# past the `Equal.trans` leaf: a `(` group of six arguments, the fifth or
# the sixth an `Equal.cong` call
def transcong.args(nn: Tree.Node) -> Bool:
  match nn:
    case Tree.NCons{Tree.Group{Lex.Tok{k, o, l, c}, +kids, cl}, after}:
      Bool.and(String.eq(o, "("),
        Bool.and(Nat.is_eq(transcong.commas(kids), 5n), transcong.fed(kids, 0n, True{}, False{})))
    case other:
      False{}

# do the node and the chain after it open a site?
def transcong.at(hh: Tree.Node, rest: Tree.Node) -> Bool:
  match hh:
    case Tree.Leaf{Lex.Tok{k, t, l, c}}:
      Bool.and(Bool.and(Lex.is_name(k), String.eq(t, "Equal.trans")), transcong.args(rest))
    case other:
      False{}

# is the token kind the lexer gives `=` or `<-`?
def transcong.bind_kind(kk: Lex.TokKind) -> Bool:
  match kk:
    case Lex.TEq{}:
      True{}
    case Lex.TBind{}:
      True{}
    case other:
      False{}

# is the node a `=` or `<-` leaf?
def transcong.binds(nn: Tree.Node) -> Bool:
  match nn:
    case Tree.Leaf{Lex.Tok{k, t, l, c}}:
      transcong.bind_kind(k)
    case other:
      False{}

# is the statement a let?
def transcong.let(sk: Tree.StmtKind) -> Bool:
  match sk:
    case Tree.SLet{}:
      True{}
    case other:
      False{}

# how many sites the node holds, at any depth; top: the node is not among a
# let's own nodes, nor after a `=` or `<-` leaf in its chain
def transcong.count(nn: Tree.Node, +top: Bool) -> Nat:
  match nn:
    case Tree.NCons{+h, +rest}:
      Nat.add(Bool.pick(Nat, Bool.and(top, transcong.at(h, rest)), 1n, 0n),
        Nat.add(transcong.count(h, True{}), transcong.count(rest, Bool.and(top, Bool.not(transcong.binds(h))))))
    case Tree.Group{o, kids, cl}:
      transcong.count(kids, True{})
    case Tree.Stmt{sk, kids, body}:
      Nat.add(transcong.count(kids, Bool.not(transcong.let(sk))), transcong.count(body, True{}))
    case other:
      0n

# LAW: over any node, transcong reports one finding for each Equal.trans an
# Equal.cong feeds as its fifth or sixth argument, outside a let's own nodes
# and after no `=` or `<-` in its chain, and none for anything else
law transcong_walk_counts:
  for nn: Tree.Node
  for +top: Bool
  for +path: String
  {List.length(&2, F.Finding, Transcong.walk(nn, top, path)) == transcong.count(nn, top) : Nat}

# LAW: transcong reports exactly those over a file's whole tree, law files and
# proof files included
law transcong_counts:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Transcong.check(Src.Src{path, text, toks, tree, bound, items}))
    == transcong.count(tree, True{}) : Nat}
