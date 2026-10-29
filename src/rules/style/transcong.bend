# rule transcong (opt-in): an `Equal.trans` that an `Equal.cong` feeds (the
# name is the two calls, as in fromrev), which a rewrite says shorter.
# `Equal.trans(T, a, b, c, Equal.cong(S, T, x => F(x), u, v, e), r)` proves
# `{F(u) == c : T}` from `r : {F(v) == c : T}`,
# and spells F(u) and F(v) out once more each, as a and b; the rewrite
# `%Equal.sym(S, u, v, e) : {F(_) == c : T}`, then `r` on the next line,
# names the motive once and drops the middle term (`%e` alone when e is
# itself an Equal.sym). With the cong last, `Equal.trans(T, a, b, c, r,
# Equal.cong(S, T, x => F(x), u, v, e))` is `%e : {a == F(_) : T}`, then `r`.
# The rewrite is a statement: in an argument it goes in parentheses,
# `(%e : P; r)`. A let has no type to check it against, so in one
# (`+q = Equal.trans(..)`) the rewrite needs an annotation and is left alone.
# Exactly: a leaf of a name kind whose text is `Equal.trans`, then, next in
# its chain, a group opened by `(` whose kids, split at their comma leaves,
# are six arguments (five comma leaves among the kids' own nodes), the fifth
# or the sixth of which is exactly a leaf of a name kind whose text is
# `Equal.cong` and a group opened by `(` (the kids end right after the group
# or go on with a comma); not among the own nodes of a let statement (a `=`
# or `<-` among its tokens, as src/syntax/tree.bend reads it) and not after
# a `=` or `<-` leaf earlier in its own chain (a let inside a group, as in a
# lambda's body written in an argument, which the tree keeps as one chain
# rather than statements: the rest of that chain is the let's value, or code
# after it the rule leaves alone), and found at any depth otherwise, under
# statements and inside groups. One finding for
# each, on the `Equal.trans` leaf. The rule reads the shape, not the types:
# a motive that `_` cannot mark (a cong under a binder of the lambda's own,
# or a chain whose middle term is not the cong's) is still reported. Laws
# and proofs are where it looks, so nothing is exempt.
import Base
import ../../src.bend as Src
import ../../finding.bend as F
import ../../syntax/lex.bend as Lex
import ../../syntax/tree.bend as Tree

# is the node a leaf of a name kind with this text?
def named(nn: Tree.Node, +tt: String) -> Bool:
  match nn:
    case Tree.Leaf{Lex.Tok{k, t, _l, _c}}:
      Bool.and(Lex.is_name(k), String.eq(t, tt))
    case _other:
      False{}

# is the node a group opened by `(`?
def paren(nn: Tree.Node) -> Bool:
  match nn:
    case Tree.Group{Lex.Tok{_k, o, _l, _c}, _kids, _cl}:
      String.eq(o, "(")
    case _other:
      False{}

# is the node a comma leaf?
def comma(nn: Tree.Node) -> Bool:
  match nn:
    case Tree.Leaf{Lex.Tok{k, _t, _l, _c}}:
      Lex.is_comma(k)
    case _other:
      False{}

# does the chain end here, or go on with a comma?
def ends(nn: Tree.Node) -> Bool:
  match nn:
    case Tree.NCons{h, _t}:
      comma(h)
    case _other:
      True{}

# past the `Equal.cong` leaf: a `(` group, then the argument's end
def cong.call(nn: Tree.Node) -> Bool:
  match nn:
    case Tree.NCons{g, after}:
      Bool.and(paren(g), ends(after))
    case _other:
      False{}

# does the chain open an argument that is exactly an `Equal.cong` call?
def cong(nn: Tree.Node) -> Bool:
  match nn:
    case Tree.NCons{h, t}:
      Bool.and(named(h, "Equal.cong"), cong.call(t))
    case _other:
      False{}

# the comma leaves among a chain's own nodes
def commas(nn: Tree.Node) -> Nat:
  match nn:
    case Tree.NCons{h, rest}:
      Nat.add(Bool.pick(Nat, comma(h), 1n, 0n), commas(rest))
    case _other:
      0n

# is an argument with nc commas before it the fifth or the sixth?
def late(+nc: Nat) -> Bool:
  Bool.or(Nat.is_eq(nc, 4n), Nat.is_eq(nc, 5n))

# from here on in a group's kids, does the fifth or sixth argument open with
# an `Equal.cong` call? nc: the commas so far; fresh: an argument opens here;
# seen: one did already
def fed(nn: Tree.Node, +nc: Nat, +fresh: Bool, +seen: Bool) -> Bool:
  match nn:
    case Tree.NCons{+h, +rest}:
      +here = Bool.and(fresh, Bool.and(late(nc), cong(Tree.NCons{h, rest})))
      +cm = comma(h)
      fed(rest, Nat.add(nc, Bool.pick(Nat, cm, 1n, 0n)), cm, Bool.or(seen, here))
    case _other:
      seen

# are a call's kids six arguments, the fifth or the sixth an `Equal.cong`?
def shape(+kids: Tree.Node) -> Bool:
  Bool.and(Nat.is_eq(commas(kids), 5n), fed(kids, 0n, True{}, False{}))

# past the `Equal.trans` leaf: a `(` group of that shape
def args(nn: Tree.Node) -> Bool:
  match nn:
    case Tree.NCons{Tree.Group{Lex.Tok{_k, o, _l, _c}, kids, _cl}, _after}:
      Bool.and(String.eq(o, "("), shape(kids))
    case _other:
      False{}

# the finding at the `Equal.trans` leaf
def cite(+ll: U32, +cc: U32, +path: String) -> F.Finding:
  F.Finding{path, ll, cc, 11, "transcong",
    "this Equal.trans is fed an Equal.cong: rewrite instead, `%e : {F(_) == c : T}` with the other proof below it, which names the motive once and drops the middle term."}

# the finding when a node and the chain after it open the shape
def site(hh: Tree.Node, rest: Tree.Node, +path: String) -> List<&2, F.Finding>:
  match hh:
    case Tree.Leaf{Lex.Tok{k, t, +l, +c}}:
      Bool.pick(List<&2, F.Finding>, Bool.and(Bool.and(Lex.is_name(k), String.eq(t, "Equal.trans")), args(rest)),
        [cite(l, c, path)], [])
    case _other:
      []

# is the node a `=` or `<-` leaf, a let's?
def binds(nn: Tree.Node) -> Bool:
  match nn:
    case Tree.Leaf{Lex.Tok{Lex.TEq{}, _t, _l, _c}}:
      True{}
    case Tree.Leaf{Lex.Tok{Lex.TBind{}, _t, _l, _c}}:
      True{}
    case _other:
      False{}

# is the statement a let?
def is_let(sk: Tree.StmtKind) -> Bool:
  match sk:
    case Tree.SLet{}:
      True{}
    case _other:
      False{}

# every site under the node, at any depth; top: the node is not among a
# let's own nodes, nor after a `=` or `<-` leaf in its chain
def walk(nn: Tree.Node, +top: Bool, +path: String) -> List<&2, F.Finding>:
  match nn:
    case Tree.NCons{+h, +rest}:
      +here = site(h, rest, path)
      List.concat(&2, F.Finding, [Bool.pick(List<&2, F.Finding>, top, here, []), walk(h, True{}, path),
        walk(rest, Bool.and(top, Bool.not(binds(h))), path)])
    case Tree.Group{_o, kids, _cl}:
      walk(kids, True{}, path)
    case Tree.Stmt{sk, kids, body}:
      List.concat(&2, F.Finding, [walk(kids, Bool.not(is_let(sk)), path), walk(body, True{}, path)])
    case _other:
      Nil{}

# the rule
def check(ss: Src.Src) -> List<&2, F.Finding>:
  Src.Src{path, _text, _toks, tree, _bound, _items} = ss
  walk(tree, True{}, path)
