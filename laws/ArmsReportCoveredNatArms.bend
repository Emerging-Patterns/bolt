# `arms` reports exactly, in a single-scrutinee match, a Nat arm already
# covered by an earlier `kn+p`, `Succ{p}` or `Succ{_}` arm.
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/syntax/bind.bend as Bind
import ../src/src.bend as Src
import ../src/syntax/tree.bend as Tree
import ../src/syntax/outline.bend as Outline
import ../src/rules/tokens.bend as T
import ../src/rules/correctness/arms.bend as Arms

# The match rules arms and twice read a case statement's pattern: its tokens
# after `case` in the tree (T.pattern), the first match column first.

# a name or `_`: what `Succ{..}` or `kn+` binds when the arm matches every Nat from there up
def arms.binder(kk: Lex.TokKind) -> Bool:
  match kk:
    case Lex.TName{}:
      True{}
    case Lex.TWild{}:
      True{}
    case other:
      False{}

# after a Nat literal, `+ p :` with p a name or `_`: the arm matches every Nat
# from the literal up
def arms.plus(rest: Tree.Node) -> Bool:
  match rest:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TOp{}, +o, l, c}},
        Tree.NCons{Tree.Leaf{Lex.Tok{b, p, l2, c2}}, Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TColon{}, s, l3, c3}}, more}}}:
      Bool.and(String.eq(o, "+"), arms.binder(b))
    case other:
      False{}

# after a Nat literal, `:`: the arm matches the literal alone
def arms.exact(rest: Tree.Node) -> Bool:
  match rest:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TColon{}, s, l, c}}, more}:
      True{}
    case other:
      False{}

# `Succ{x}` with x one name or `_`: every Nat from 1 up
def arms.succ(+tt: String, kk: Lex.TokKind) -> Bool:
  Bool.and(String.eq(tt, "Succ"), arms.binder(kk))

# a Nat literal's value k, when what follows it makes the arm one that counts
def arms.num(mm: Maybe<&2, U32>, +when: Bool) -> Maybe<&2, U32>:
  match mm:
    case None{}:
      None{}
    case Some{k}:
      Bool.pick(Maybe<&2, U32>, when, Some{k}, None{})

# k when the pattern matches every Nat from k up: `kn+p:`, or `Succ{p}` and
# `Succ{_}` (k is 1); none for any other pattern
def arms.from(pat: Tree.Node) -> Maybe<&2, U32>:
  match pat:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TNum{}, +t, l, c}}, rest}:
      arms.num(T.nat_value(t), arms.plus(rest))
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TUpper{}, +t, l, c}},
        Tree.NCons{Tree.Group{open, Tree.NCons{Tree.Leaf{Lex.Tok{k, p, l2, c2}}, Tree.NNil{}}, close}, more}}:
      Bool.pick(Maybe<&2, U32>, arms.succ(t, k), Some{1}, None{})
    case other:
      None{}

# the least Nat a Nat arm matches: k for `kn:` and `kn+p:`, 1 for `Succ{p}`
# and `Succ{_}`; none for any other pattern
def arms.least(pat: Tree.Node) -> Maybe<&2, U32>:
  match pat:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TNum{}, +t, l, c}}, +rest}:
      arms.num(T.nat_value(t), Bool.or(arms.plus(rest), arms.exact(rest)))
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TUpper{}, +t, l, c}},
        Tree.NCons{Tree.Group{open, Tree.NCons{Tree.Leaf{Lex.Tok{k, p, l2, c2}}, Tree.NNil{}}, close}, more}}:
      Bool.pick(Maybe<&2, U32>, arms.succ(t, k), Some{1}, None{})
    case other:
      None{}

# an arm is covered when its least Nat is at or above low, the least k of the
# from-k-up arms above it
def arms.hit(low: Maybe<&2, U32>, least: Maybe<&2, U32>) -> Bool:
  match low least:
    case None{} m:
      False{}
    case Some{k} None{}:
      False{}
    case Some{k} Some{j}:
      U32.is_ge(j, k)

# the least k of the from-k-up arms so far, once one more arm is read
def arms.lower(low: Maybe<&2, U32>, from: Maybe<&2, U32>) -> Maybe<&2, U32>:
  match low from:
    case None{} f:
      f
    case Some{k} None{}:
      Some{k}
    case Some{+k} Some{+j}:
      Bool.pick(Maybe<&2, U32>, U32.is_lt(j, k), Some{j}, Some{k})

# how many of a match's case arms an earlier from-k-up arm already covers,
# low the least k of those above them
def arms.covered(body: Tree.Node, +low: Maybe<&2, U32>) -> Nat:
  match body:
    case Tree.NCons{Tree.Stmt{Tree.SCase{}, kids, b}, rest}:
      +pat = T.pattern(kids)
      +m = arms.covered(rest, arms.lower(low, arms.from(pat)))
      Bool.pick(Nat, arms.hit(low, arms.least(pat)), 1n+m, m)
    case Tree.NCons{h, rest}:
      arms.covered(rest, low)
    case other:
      0n

# a statement's own tokens are `match x:`: one scrutinee
def arms.single(kids: Tree.Node) -> Bool:
  match kids:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TKey{}, +t, l, c}},
        Tree.NCons{x, Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TColon{}, s, l2, c2}}, Tree.NNil{}}}}:
      String.eq(t, "match")
    case other:
      False{}

# how many covered arms the single-scrutinee matches under the node hold, at
# any depth
def arms_count(nn: Tree.Node) -> Nat:
  match nn:
    case Tree.NCons{Tree.Stmt{kind, kids, +body}, rest}:
      Nat.add(Bool.pick(Nat, arms.single(kids), arms.covered(body, None{}), 0n),
        Nat.add(arms_count(body), arms_count(rest)))
    case Tree.NCons{h, rest}:
      arms_count(rest)
    case other:
      0n

# LAW: arms reports one finding for each case arm of a single-scrutinee
# match, at any depth, whose least Nat an earlier `kn+p`, `Succ{p}` or
# `Succ{_}` arm of the same match already matches, and none for any other arm
law arms_counts:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for +tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Arms.check(Src.Src{path, text, toks, tree, bound, items})) == arms_count(tree) : Nat}
