# proofs of laws/TreeKeepsEveryToken.bend
import Base
import ../src/syntax/lex.bend as Lex
import ../src/syntax/tree.bend as Tree
import ../src/lazy/lazy.bend as Lazy
import ../laws/TreeKeepsEveryToken.bend as Laws
import ./lemmas/LexAndTreeFacts.bend as M1

# the tree (laws/TreeKeepsEveryToken.bend)
# ---------------------
# The machine's stack is read as the leaves it holds so far, newest first:
# vg is that list while the stack is well formed, None when it is not. Every
# step keeps it the reversed leaves of the tokens read, so the finished tree
# reads them back in order.

# Unit for None, Empty for Some: a motive that tells them apart
def none_ty(mm: Maybe<&2, List<&2, Lex.Tok>>) -> Type:
  match mm:
    case None{}:
      Unit
    case Some{_a}:
      Empty

# None is never Some
law none_some:
  for -a: List<&2, Lex.Tok>
  for e: {None{} == Some{a} : Maybe<&2, List<&2, Lex.Tok>>}
  Empty

def none_some(_a, e):
  %e : none_ty(_)
  Unit{}

# Unit for 0, Empty for a successor
def zero_ty(nn: Nat) -> Type:
  match nn:
    case Zero{}:
      Unit
    case Succ{_p}:
      Empty

# 0 is never a successor
law zero_succ:
  for -p: Nat
  for e: {0n == 1n+p : Nat}
  Empty

def zero_succ(_p, e):
  %e : zero_ty(_)
  Unit{}

# a group's close, if any, onto a known list
def m_close(mm: Maybe<&2, List<&2, Lex.Tok>>, close: Maybe<&2, Lex.Tok>) -> Maybe<&2, List<&2, Lex.Tok>>:
  match mm:
    case None{}:
      None{}
    case Some{a}:
      Some{Tree.leaf_close(close, a)}

# tokens, in order, onto a known list
def m_toks(mm: Maybe<&2, List<&2, Lex.Tok>>, xs: List<&2, Lex.Tok>) -> Maybe<&2, List<&2, Lex.Tok>>:
  match mm:
    case None{}:
      None{}
    case Some{a}:
      Some{List.reverse.go(&2, Lex.Tok, xs, a)}

# a chain reversed onto another, read: the first's leaves, then the other's
law rev:
  for +x: Tree.Node
  for +m: Tree.Node
  for +acc: List<&2, Lex.Tok>
  {Tree.leaves.go(Tree.reverse(x, m), acc) == Tree.leaves.go(m, M1.rgo(x, acc)) : List<&2, Lex.Tok>}

def rev(x, m, acc):
  match x:
    case Tree.NCons{h, t}:
      rev(t, Tree.NCons{h, m}, acc)
    case Tree.Leaf{_tok}:
      {==}
    case Tree.Group{_o, _k, _c}:
      {==}
    case Tree.Stmt{_kd, _k, _b}:
      {==}
    case Tree.NNil{}:
      {==}

# a closed group's leaves: its bracket, its kids, then its close, if any
law close.m:
  for +mm: Maybe<&2, List<&2, Lex.Tok>>
  for +o: Lex.Tok
  for +k: Tree.Node
  for +cl: Maybe<&2, Lex.Tok>
  {M1.m_leaf(mm, Tree.Group{o, Tree.reverse(k, Tree.NNil{}), cl}) == m_close(M1.m_group(mm, o, k), cl)
    : Maybe<&2, List<&2, Lex.Tok>>}

def close.m(mm, o, k, cl):
  match mm:
    case None{}:
      {==}
    case Some{a}:
      Equal.cong(List<&2, Lex.Tok>, Maybe<&2, List<&2, Lex.Tok>>, x => Some{Tree.leaf_close(cl, x)},
        Tree.leaves.go(Tree.reverse(k, Tree.NNil{}), o <> a), M1.rgo(k, o <> a), rev(k, Tree.NNil{}, o <> a))

# closing the group on top adds its close to the leaves
law close.group:
  for +o: Lex.Tok
  for +k: Tree.Node
  for +rest: List<&2, Tree.Frame>
  for +cl: Maybe<&2, Lex.Tok>
  {M1.vg(Tree.close_one(Tree.FGroup{o, k} <> rest, cl)) == m_close(M1.vg(Tree.FGroup{o, k} <> rest), cl)
    : Maybe<&2, List<&2, Lex.Tok>>}

def close.group(o, k, rest, cl):
  Equal.trans(Maybe<&2, List<&2, Lex.Tok>>,
    M1.vg(Tree.put(rest, Tree.Group{o, Tree.reverse(k, Tree.NNil{}), cl})),
    M1.m_leaf(M1.vg(rest), Tree.Group{o, Tree.reverse(k, Tree.NNil{}), cl}),
    m_close(M1.m_group(M1.vg(rest), o, k), cl),
    M1.put(rest, Tree.Group{o, Tree.reverse(k, Tree.NNil{}), cl}),
    close.m(M1.vg(rest), o, k, cl))

# no close adds nothing
law m_close.none:
  for +mm: Maybe<&2, List<&2, Lex.Tok>>
  {m_close(mm, None{}) == mm : Maybe<&2, List<&2, Lex.Tok>>}

def m_close.none(mm):
  match mm:
    case None{}:
      {==}
    case Some{_a}:
      {==}

# a group closed by nothing keeps the leaves
law close.none:
  for +s: List<&2, Tree.Frame>
  {M1.vg(Tree.close_one(s, None{})) == M1.vg(s) : Maybe<&2, List<&2, Lex.Tok>>}

def close.none(s):
  match s:
    case Con{Tree.FGroup{o, k}, rest}:
      Equal.trans(Maybe<&2, List<&2, Lex.Tok>>,
        M1.vg(Tree.close_one(Tree.FGroup{o, k} <> rest, None{})),
        m_close(M1.vg(Tree.FGroup{o, k} <> rest), None{}),
        M1.vg(Tree.FGroup{o, k} <> rest),
        close.group(o, k, rest, None{}),
        m_close.none(M1.vg(Tree.FGroup{o, k} <> rest)))
    case Con{Tree.FStmt{_i, _k, _b}, _rest}:
      {==}
    case Con{Tree.FRoot{_b}, _rest}:
      {==}
    case Nil{}:
      {==}

# groups closed by nothing keep the leaves
law close_n.none:
  for +n: Nat
  for +s: List<&2, Tree.Frame>
  {M1.vg(Tree.close_n(n, s, None{})) == M1.vg(s) : Maybe<&2, List<&2, Lex.Tok>>}

def close_n.none(n, s):
  match n:
    case Zero{}:
      {==}
    case Succ{Zero{}}:
      close.none(s)
    case Succ{Succ{q}}:
      Equal.trans(Maybe<&2, List<&2, Lex.Tok>>,
        M1.vg(Tree.close_n(1n+q, Tree.close_one(s, None{}), None{})),
        M1.vg(Tree.close_one(s, None{})),
        M1.vg(s),
        close_n.none(1n+q, Tree.close_one(s, None{})),
        close.none(s))

# closing every group keeps the leaves
law close_all:
  for +s: List<&2, Tree.Frame>
  {M1.vg(Tree.close_all(s)) == M1.vg(s) : Maybe<&2, List<&2, Lex.Tok>>}

def close_all(s):
  close_n.none(Tree.groups(s), s)

# are the top n frames of the stack all open groups?
def at_least(nn: Nat, stack: List<&2, Tree.Frame>) -> Bool:
  match nn stack:
    case Zero{} _s:
      True{}
    case Succ{p} Con{Tree.FGroup{_o, _k}, rest}:
      at_least(p, rest)
    case Succ{_p} _other:
      False{}

# a put leaves the frames' kinds as they were
law at_least.put:
  for +n: Nat
  for +s: List<&2, Tree.Frame>
  for +x: Tree.Node
  {at_least(n, Tree.put(s, x)) == at_least(n, s) : Bool}

def at_least.put(n, s, _x):
  match n s:
    case Zero{} _s:
      {==}
    case Succ{_p} Nil{}:
      {==}
    case Succ{_p} Con{Tree.FGroup{_o, _k}, _rest}:
      {==}
    case Succ{_p} Con{Tree.FStmt{_i, _k, _b}, _rest}:
      {==}
    case Succ{_p} Con{Tree.FRoot{_b}, _rest}:
      {==}

# whichever count the search stops on, the groups are there
law al.stop:
  for +b: Bool
  for -x: Nat
  for -f: Unit -> Nat
  for -s: List<&2, Tree.Frame>
  for ex: {at_least(x, s) == True{} : Bool}
  for ef: {at_least(f(Unit{}), s) == True{} : Bool}
  {at_least(Lazy.stop(Nat, b, x, f), s) == True{} : Bool}

def al.stop(b, _x, _f, _s, ex, ef):
  match b:
    case True{}:
      ex
    case False{}:
      ef

# one more group above the ones found below
law al.up:
  for +d: Nat
  for -o: Lex.Tok
  for -k: Tree.Node
  for -rest: List<&2, Tree.Frame>
  for e: {at_least(d, rest) == True{} : Bool}
  {at_least(Tree.depth_to.up(d), Tree.FGroup{o, k} <> rest) == True{} : Bool}

def al.up(d, _o, _k, _rest, e):
  match d:
    case Zero{}:
      {==}
    case Succ{_p}:
      e

# the groups a close bracket reaches down to are all open groups
law at_least.depth:
  for +s: List<&2, Tree.Frame>
  for +cc: String
  {at_least(Tree.depth_to(s, cc), s) == True{} : Bool}

def at_least.depth(s, cc):
  match s:
    case Con{Tree.FGroup{Lex.Tok{k, t, l, c2}, kids}, rest}:
      al.stop(String.eq(Tree.closer(t), cc), 1n,
        _u => Lazy.stop(Nat, String.eq(cc, ">"), 0n, _v => Tree.depth_to.up(Tree.depth_to(rest, cc))),
        Tree.FGroup{Lex.Tok{k, t, l, c2}, kids} <> rest, {==},
        al.stop(String.eq(cc, ">"), 0n, _v => Tree.depth_to.up(Tree.depth_to(rest, cc)),
          Tree.FGroup{Lex.Tok{k, t, l, c2}, kids} <> rest, {==},
          al.up(Tree.depth_to(rest, cc), Lex.Tok{k, t, l, c2}, kids, rest, at_least.depth(rest, cc))))
    case Con{Tree.FStmt{_i, _k, _b}, _rest}:
      {==}
    case Con{Tree.FRoot{_b}, _rest}:
      {==}
    case Nil{}:
      {==}

# closing groups that are all there adds the close, if any, to the leaves
law close_n.some:
  for +p: Nat
  for +s: List<&2, Tree.Frame>
  for +cl: Maybe<&2, Lex.Tok>
  for e: {at_least(1n+p, s) == True{} : Bool}
  {M1.vg(Tree.close_n(1n+p, s, cl)) == m_close(M1.vg(s), cl) : Maybe<&2, List<&2, Lex.Tok>>}

def close_n.some(p, s, cl, e):
  match p s:
    case Zero{} Con{Tree.FGroup{o, k}, rest}:
      close.group(o, k, rest, cl)
    case Succ{q} Con{Tree.FGroup{o, k}, rest}:
      Equal.trans(Maybe<&2, List<&2, Lex.Tok>>,
        M1.vg(Tree.close_n(1n+q, Tree.put(rest, Tree.Group{o, Tree.reverse(k, Tree.NNil{}), None{}}), cl)),
        m_close(M1.vg(Tree.put(rest, Tree.Group{o, Tree.reverse(k, Tree.NNil{}), None{}})), cl),
        m_close(M1.vg(Tree.FGroup{o, k} <> rest), cl),
        close_n.some(q, Tree.put(rest, Tree.Group{o, Tree.reverse(k, Tree.NNil{}), None{}}), cl,
          Equal.trans(Bool, at_least(1n+q, Tree.put(rest, Tree.Group{o, Tree.reverse(k, Tree.NNil{}), None{}})),
            at_least(1n+q, rest), True{},
            at_least.put(1n+q, rest, Tree.Group{o, Tree.reverse(k, Tree.NNil{}), None{}}), e)),
        Equal.cong(Maybe<&2, List<&2, Lex.Tok>>, Maybe<&2, List<&2, Lex.Tok>>, m => m_close(m, cl),
          M1.vg(Tree.close_one(Tree.FGroup{o, k} <> rest, None{})), M1.vg(Tree.FGroup{o, k} <> rest),
          close.none(Tree.FGroup{o, k} <> rest)))
    case _p Nil{}:
      Empty.absurd({M1.vg(Tree.close_n(1n+_p, [], cl)) == m_close(M1.vg([]), cl) : Maybe<&2, List<&2, Lex.Tok>>},
        M1.false_true(e))
    case _p Con{Tree.FStmt{i, k, b}, rest}:
      Empty.absurd({M1.vg(Tree.close_n(1n+_p, Tree.FStmt{i, k, b} <> rest, cl))
        == m_close(M1.vg(Tree.FStmt{i, k, b} <> rest), cl) : Maybe<&2, List<&2, Lex.Tok>>},
        M1.false_true(e))
    case _p Con{Tree.FRoot{b}, rest}:
      Empty.absurd({M1.vg(Tree.close_n(1n+_p, Tree.FRoot{b} <> rest, cl))
        == m_close(M1.vg(Tree.FRoot{b} <> rest), cl) : Maybe<&2, List<&2, Lex.Tok>>},
        M1.false_true(e))

# a close that closes a group is that group's last leaf
law m_close.some:
  for +mm: Maybe<&2, List<&2, Lex.Tok>>
  for +tok: Lex.Tok
  {m_close(mm, Some{tok}) == M1.m_leaf(mm, Tree.Leaf{tok}) : Maybe<&2, List<&2, Lex.Tok>>}

def m_close.some(mm, _tok):
  match mm:
    case None{}:
      {==}
    case Some{_a}:
      {==}

# a close bracket is a leaf: a stray one when it reaches no group, else the
# close of the group it reaches
law close.to:
  for +n: Nat
  for +s: List<&2, Tree.Frame>
  for +tok: Lex.Tok
  for e: {at_least(n, s) == True{} : Bool}
  {M1.vg(Lazy.stop(List<&2, Tree.Frame>, Nat.is_eq(n, 0n), Tree.put(s, Tree.Leaf{tok}),
    _u => Tree.close_n(n, s, Some{tok}))) == M1.m_leaf(M1.vg(s), Tree.Leaf{tok}) : Maybe<&2, List<&2, Lex.Tok>>}

def close.to(n, s, tok, e):
  match n:
    case Zero{}:
      M1.put(s, Tree.Leaf{tok})
    case Succ{p}:
      Equal.trans(Maybe<&2, List<&2, Lex.Tok>>,
        M1.vg(Tree.close_n(1n+p, s, Some{tok})),
        m_close(M1.vg(s), Some{tok}),
        M1.m_leaf(M1.vg(s), Tree.Leaf{tok}),
        close_n.some(p, s, Some{tok}, e),
        m_close.some(M1.vg(s), tok))

# a close bracket adds itself to the leaves
law close_tok:
  for +s: List<&2, Tree.Frame>
  for +k: Lex.TokKind
  for +t: String
  for +l: U32
  for +c: U32
  {M1.vg(Tree.close_tok(s, Lex.Tok{k, t, l, c})) == M1.m_leaf(M1.vg(s), Tree.Leaf{Lex.Tok{k, t, l, c}})
    : Maybe<&2, List<&2, Lex.Tok>>}

def close_tok(s, k, t, l, c):
  close.to(Tree.depth_to(s, t), s, Lex.Tok{k, t, l, c}, at_least.depth(s, t))

# no tokens add nothing
law m_toks.nil:
  for +mm: Maybe<&2, List<&2, Lex.Tok>>
  {m_toks(mm, []) == mm : Maybe<&2, List<&2, Lex.Tok>>}

def m_toks.nil(mm):
  match mm:
    case None{}:
      {==}
    case Some{_a}:
      {==}

# a leaf is its one token
law m_toks.one:
  for +mm: Maybe<&2, List<&2, Lex.Tok>>
  for +tok: Lex.Tok
  {M1.m_leaf(mm, Tree.Leaf{tok}) == m_toks(mm, [tok]) : Maybe<&2, List<&2, Lex.Tok>>}

def m_toks.one(mm, _tok):
  match mm:
    case None{}:
      {==}
    case Some{_a}:
      {==}

# a leaf, then tokens: the leaf's token first
law m_toks.con:
  for +mm: Maybe<&2, List<&2, Lex.Tok>>
  for +tok: Lex.Tok
  for +ys: List<&2, Lex.Tok>
  {m_toks(M1.m_leaf(mm, Tree.Leaf{tok}), ys) == m_toks(mm, tok <> ys) : Maybe<&2, List<&2, Lex.Tok>>}

def m_toks.con(mm, _tok, _ys):
  match mm:
    case None{}:
      {==}
    case Some{_a}:
      {==}

# a run of `>` adds one `>` per char
law close_gts:
  for +cs: List<&2, Char>
  for +s: List<&2, Tree.Frame>
  for +l: U32
  for +c: U32
  {M1.vg(Tree.close_gts(cs, s, l, c)) == m_toks(M1.vg(s), Laws.gts(cs, l, c)) : Maybe<&2, List<&2, Lex.Tok>>}

def close_gts(cs, s, l, c):
  match cs:
    case Nil{}:
      Equal.sym(Maybe<&2, List<&2, Lex.Tok>>, m_toks(M1.vg(s), []), M1.vg(s), m_toks.nil(M1.vg(s)))
    case Con{_ch, t}:
      Equal.trans(Maybe<&2, List<&2, Lex.Tok>>,
        M1.vg(Tree.close_gts(t, Tree.close_tok(s, Lex.Tok{Lex.TOp{}, ">", l, c}), l, (c + 1 : U32))),
        m_toks(M1.vg(Tree.close_tok(s, Lex.Tok{Lex.TOp{}, ">", l, c})), Laws.gts(t, l, (c + 1 : U32))),
        m_toks(M1.vg(s), Lex.Tok{Lex.TOp{}, ">", l, c} <> Laws.gts(t, l, (c + 1 : U32))),
        close_gts(t, Tree.close_tok(s, Lex.Tok{Lex.TOp{}, ">", l, c}), l, (c + 1 : U32)),
        Equal.trans(Maybe<&2, List<&2, Lex.Tok>>,
          m_toks(M1.vg(Tree.close_tok(s, Lex.Tok{Lex.TOp{}, ">", l, c})), Laws.gts(t, l, (c + 1 : U32))),
          m_toks(M1.m_leaf(M1.vg(s), Tree.Leaf{Lex.Tok{Lex.TOp{}, ">", l, c}}), Laws.gts(t, l, (c + 1 : U32))),
          m_toks(M1.vg(s), Lex.Tok{Lex.TOp{}, ">", l, c} <> Laws.gts(t, l, (c + 1 : U32))),
          Equal.cong(Maybe<&2, List<&2, Lex.Tok>>, Maybe<&2, List<&2, Lex.Tok>>,
            m => m_toks(m, Laws.gts(t, l, (c + 1 : U32))),
            M1.vg(Tree.close_tok(s, Lex.Tok{Lex.TOp{}, ">", l, c})),
            M1.m_leaf(M1.vg(s), Tree.Leaf{Lex.Tok{Lex.TOp{}, ">", l, c}}),
            close_tok(s, Lex.TOp{}, ">", l, c)),
          m_toks.con(M1.vg(s), Lex.Tok{Lex.TOp{}, ">", l, c}, Laws.gts(t, l, (c + 1 : U32)))))

# a close adds a run of `>` split, or itself
law close_any.at:
  for +gt: Bool
  for +s: List<&2, Tree.Frame>
  for +k: Lex.TokKind
  for +t: String
  for +l: U32
  for +c: U32
  {M1.vg(Tree.close_any.at(gt, s, Lex.Tok{k, t, l, c}, t, l, c))
    == m_toks(M1.vg(s), Bool.pick(List<&2, Lex.Tok>, gt, Laws.gts(String.to_list(t), l, c), [Lex.Tok{k, t, l, c}]))
    : Maybe<&2, List<&2, Lex.Tok>>}

def close_any.at(gt, s, k, t, l, c):
  match gt:
    case True{}:
      close_gts(String.to_list(t), s, l, c)
    case False{}:
      Equal.trans(Maybe<&2, List<&2, Lex.Tok>>,
        M1.vg(Tree.close_tok(s, Lex.Tok{k, t, l, c})),
        M1.m_leaf(M1.vg(s), Tree.Leaf{Lex.Tok{k, t, l, c}}),
        m_toks(M1.vg(s), [Lex.Tok{k, t, l, c}]),
        close_tok(s, k, t, l, c),
        m_toks.one(M1.vg(s), Lex.Tok{k, t, l, c}))

# an open bracket's leaves so far: itself
law m_group.one:
  for +mm: Maybe<&2, List<&2, Lex.Tok>>
  for +tok: Lex.Tok
  {M1.m_group(mm, tok, Tree.NNil{}) == m_toks(mm, [tok]) : Maybe<&2, List<&2, Lex.Tok>>}

def m_group.one(mm, _tok):
  match mm:
    case None{}:
      {==}
    case Some{_a}:
      {==}

# an opener or a leaf adds itself
law push.leaf:
  for +o: Bool
  for +s: List<&2, Tree.Frame>
  for +tok: Lex.Tok
  {M1.vg(Bool.pick(List<&2, Tree.Frame>, o, Tree.FGroup{tok, Tree.NNil{}} <> s, Tree.put(s, Tree.Leaf{tok})))
    == m_toks(M1.vg(s), [tok]) : Maybe<&2, List<&2, Lex.Tok>>}

def push.leaf(o, s, tok):
  match o:
    case True{}:
      m_group.one(M1.vg(s), tok)
    case False{}:
      Equal.trans(Maybe<&2, List<&2, Lex.Tok>>,
        M1.vg(Tree.put(s, Tree.Leaf{tok})),
        M1.m_leaf(M1.vg(s), Tree.Leaf{tok}),
        m_toks(M1.vg(s), [tok]),
        M1.put(s, Tree.Leaf{tok}),
        m_toks.one(M1.vg(s), tok))

# a token pushed adds itself, or, when it closes, what its close adds
law push.at:
  for +b: Bool
  for +o: Bool
  for +s: List<&2, Tree.Frame>
  for +k: Lex.TokKind
  for +t: String
  for +l: U32
  for +c: U32
  {M1.vg(Lazy.stop(List<&2, Tree.Frame>, Bool.not(b),
      Bool.pick(List<&2, Tree.Frame>, o, Tree.FGroup{Lex.Tok{k, t, l, c}, Tree.NNil{}} <> s,
        Tree.put(s, Tree.Leaf{Lex.Tok{k, t, l, c}})),
      _u => Tree.close_any(s, Lex.Tok{k, t, l, c})))
    == m_toks(M1.vg(s), Bool.pick(List<&2, Lex.Tok>, Bool.not(b), [Lex.Tok{k, t, l, c}],
      Bool.pick(List<&2, Lex.Tok>, String.starts_with(t, ">"), Laws.gts(String.to_list(t), l, c),
        [Lex.Tok{k, t, l, c}])))
    : Maybe<&2, List<&2, Lex.Tok>>}

def push.at(b, o, s, k, t, l, c):
  match b:
    case True{}:
      close_any.at(String.starts_with(t, ">"), s, k, t, l, c)
    case False{}:
      push.leaf(o, s, Lex.Tok{k, t, l, c})

# what the tree adds for a significant token: itself, or, when it closes,
# what its close adds
def code_adds(+k: Lex.TokKind, +t: String, +l: U32, +c: U32) -> List<&2, Lex.Tok>:
  Bool.pick(List<&2, Lex.Tok>, Bool.not(Tree.closes_with(k, t)), [Lex.Tok{k, t, l, c}],
    Bool.pick(List<&2, Lex.Tok>, String.starts_with(t, ">"), Laws.gts(String.to_list(t), l, c), [Lex.Tok{k, t, l, c}]))

# a token pushed adds itself, or, when it closes, what its close adds
law push:
  for +s: List<&2, Tree.Frame>
  for +k: Lex.TokKind
  for +t: String
  for +l: U32
  for +c: U32
  for +g: Bool
  {M1.vg(Tree.push(s, Lex.Tok{k, t, l, c}, g))
    == m_toks(M1.vg(s), code_adds(k, t, l, c))
    : Maybe<&2, List<&2, Lex.Tok>>}

def push(s, k, t, l, c, g):
  push.at(Tree.closes_with(k, t), Bool.or(Lex.is_open(k), Tree.opens_angle(k, t, g)), s, k, t, l, c)

# the tree's test for a run of `>` is the law's
law only_gt:
  for +cs: List<&2, Char>
  {Laws.only_gt(cs) == Tree.all_gt(cs) : Bool}

def only_gt(cs):
  match cs:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.cong(Bool, Bool, x => Lazy.and_then(Char.is_eq(h, '>'), _u => x),
        Laws.only_gt(t), Tree.all_gt(t), only_gt(t))

# picking on a negation swaps the branches
law not_pick:
  for +x: Bool
  for +a: List<&2, Lex.Tok>
  for +b: List<&2, Lex.Tok>
  {Bool.pick(List<&2, Lex.Tok>, Bool.not(x), a, b) == Bool.pick(List<&2, Lex.Tok>, x, b, a) : List<&2, Lex.Tok>}

def not_pick(x, _a, _b):
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

# an operator past its first char, by whether that char is a `>`
law decide.op:
  for +b: Bool
  for +r: String
  for +gs: List<&2, Lex.Tok>
  for +one: List<&2, Lex.Tok>
  {Bool.pick(List<&2, Lex.Tok>, Bool.not(Lazy.and_then(b, _u => Tree.all_gt(String.to_list(r)))), one,
      Bool.pick(List<&2, Lex.Tok>, String.starts_with.go.if(SNil{}, r, b), gs, one))
    == Bool.pick(List<&2, Lex.Tok>, Lazy.and_then(b, _u => Laws.only_gt(String.to_list(r))), gs, one)
    : List<&2, Lex.Tok>}

def decide.op(b, r, gs, one):
  match b:
    case False{}:
      {==}
    case True{}:
      %M1.starts_nil(r) :
        {Bool.pick(List<&2, Lex.Tok>, Bool.not(Tree.all_gt(String.to_list(r))), one,
          Bool.pick(List<&2, Lex.Tok>, _, gs, one))
          == Bool.pick(List<&2, Lex.Tok>, Laws.only_gt(String.to_list(r)), gs, one) : List<&2, Lex.Tok>}
      %only_gt(String.to_list(r)) :
        {Bool.pick(List<&2, Lex.Tok>, Bool.not(_), one, gs)
          == Bool.pick(List<&2, Lex.Tok>, Laws.only_gt(String.to_list(r)), gs, one) : List<&2, Lex.Tok>}
      not_pick(Laws.only_gt(String.to_list(r)), one, gs)

# the tree splits a token exactly when the law says it is a run of `>`
law decide:
  for +k: Lex.TokKind
  for +t: String
  for +l: U32
  for +c: U32
  {code_adds(k, t, l, c)
    == M1.law_adds(k, t, l, c)
    : List<&2, Lex.Tok>}

def decide(k, t, l, c):
  match k t:
    case Lex.TOp{} SNil{}:
      {==}
    case Lex.TOp{} SCon{h, r}:
      decide.op(Char.is_eq(h, '>'), r, Laws.gts(String.to_list(SCon{h, r}), l, c),
        [Lex.Tok{Lex.TOp{}, SCon{h, r}, l, c}])
    case Lex.TClose{} _t:
      {==}
    case Lex.TName{} _t:
      {==}
    case Lex.TUpper{} _t:
      {==}
    case Lex.TDotted{} _t:
      {==}
    case Lex.TWild{} _t:
      {==}
    case Lex.TKey{} _t:
      {==}
    case Lex.TNum{} _t:
      {==}
    case Lex.TStr{} _t:
      {==}
    case Lex.TChar{} _t:
      {==}
    case Lex.TComment{} _t:
      {==}
    case Lex.TSpace{} _t:
      {==}
    case Lex.TNewline{} _t:
      {==}
    case Lex.TColon{} _t:
      {==}
    case Lex.TEq{} _t:
      {==}
    case Lex.TBind{} _t:
      {==}
    case Lex.TArrow{} _t:
      {==}
    case Lex.TLam{} _t:
      {==}
    case Lex.TAll{} _t:
      {==}
    case Lex.TAmp{} _t:
      {==}
    case Lex.TOpen{} _t:
      {==}
    case Lex.TComma{} _t:
      {==}

# a finished statement's leaves: its kids, then its body
law stmt_leaves:
  for +kd: Tree.StmtKind
  for +k: Tree.Node
  for +b: Tree.Node
  for +acc: List<&2, Lex.Tok>
  {Tree.leaves.go(Tree.Stmt{kd, Tree.reverse(k, Tree.NNil{}), Tree.reverse(b, Tree.NNil{})}, acc)
    == M1.rgo(b, M1.rgo(k, acc)) : List<&2, Lex.Tok>}

def stmt_leaves(_kd, k, b, acc):
  Equal.trans(List<&2, Lex.Tok>,
    Tree.leaves.go(Tree.reverse(b, Tree.NNil{}), Tree.leaves.go(Tree.reverse(k, Tree.NNil{}), acc)),
    Tree.leaves.go(Tree.reverse(b, Tree.NNil{}), M1.rgo(k, acc)),
    M1.rgo(b, M1.rgo(k, acc)),
    Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, x => Tree.leaves.go(Tree.reverse(b, Tree.NNil{}), x),
      Tree.leaves.go(Tree.reverse(k, Tree.NNil{}), acc), M1.rgo(k, acc), rev(k, Tree.NNil{}, acc)),
    rev(b, Tree.NNil{}, M1.rgo(k, acc)))

# a finished statement put in its parent's body keeps the leaves
law end.m:
  for +mm: Maybe<&2, List<&2, Lex.Tok>>
  for +k2: Tree.Node
  for +b2: Tree.Node
  for +kd: Tree.StmtKind
  for +k: Tree.Node
  for +b: Tree.Node
  {M1.m_stmt(mm, k2, Tree.NCons{Tree.Stmt{kd, Tree.reverse(k, Tree.NNil{}), Tree.reverse(b, Tree.NNil{})}, b2})
    == M1.m_stmt(M1.m_stmt(mm, k2, b2), k, b) : Maybe<&2, List<&2, Lex.Tok>>}

def end.m(mm, k2, b2, kd, k, b):
  match mm:
    case None{}:
      {==}
    case Some{a}:
      Equal.cong(List<&2, Lex.Tok>, Maybe<&2, List<&2, Lex.Tok>>, x => Some{x},
        Tree.leaves.go(Tree.Stmt{kd, Tree.reverse(k, Tree.NNil{}), Tree.reverse(b, Tree.NNil{})}, M1.rgo(b2, M1.rgo(k2,
            a))),
        M1.rgo(b, M1.rgo(k, M1.rgo(b2, M1.rgo(k2, a)))),
        stmt_leaves(kd, k, b, M1.rgo(b2, M1.rgo(k2, a))))

# finishing the innermost statement keeps the leaves
law end_stmt:
  for +s: List<&2, Tree.Frame>
  {M1.vs(Tree.end_stmt(s)) == M1.vs(s) : Maybe<&2, List<&2, Lex.Tok>>}

def end_stmt(s):
  match s:
    case Con{Tree.FStmt{_i, k, b}, Con{Tree.FStmt{_i2, k2, b2}, r2}}:
      end.m(M1.vs(r2), k2, b2, Tree.classify(Tree.reverse(k, Tree.NNil{})), k, b)
    case Con{Tree.FStmt{_i, k, b}, Con{Tree.FRoot{bd}, _r2}}:
      Equal.cong(List<&2, Lex.Tok>, Maybe<&2, List<&2, Lex.Tok>>, x => Some{x},
        Tree.leaves.go(Tree.Stmt{Tree.classify(Tree.reverse(k, Tree.NNil{})), Tree.reverse(k, Tree.NNil{}),
          Tree.reverse(b, Tree.NNil{})}, M1.rgo(bd, [])),
        M1.rgo(b, M1.rgo(k, M1.rgo(bd, []))),
        stmt_leaves(Tree.classify(Tree.reverse(k, Tree.NNil{})), k, b, M1.rgo(bd, [])))
    case Con{Tree.FStmt{_i, _k, _b}, Con{Tree.FGroup{_o, _k2}, _r2}}:
      {==}
    case Con{Tree.FStmt{_i, _k, _b}, Nil{}}:
      {==}
    case Con{Tree.FGroup{_o, _k}, _rest}:
      {==}
    case Con{Tree.FRoot{_b}, _rest}:
      {==}
    case Nil{}:
      {==}

# finishing statements keeps the leaves
law end_n:
  for +n: Nat
  for +s: List<&2, Tree.Frame>
  {M1.vs(Tree.end_n(n, s)) == M1.vs(s) : Maybe<&2, List<&2, Lex.Tok>>}

def end_n(n, s):
  match n:
    case Zero{}:
      {==}
    case Succ{p}:
      Equal.trans(Maybe<&2, List<&2, Lex.Tok>>,
        M1.vs(Tree.end_n(p, Tree.end_stmt(s))), M1.vs(Tree.end_stmt(s)), M1.vs(s),
        end_n(p, Tree.end_stmt(s)), end_stmt(s))

# an empty statement adds nothing
law m_stmt.nil:
  for +mm: Maybe<&2, List<&2, Lex.Tok>>
  {M1.m_stmt(mm, Tree.NNil{}, Tree.NNil{}) == mm : Maybe<&2, List<&2, Lex.Tok>>}

def m_stmt.nil(mm):
  match mm:
    case None{}:
      {==}
    case Some{_a}:
      {==}

# a new statement over the ones it leaves open keeps the leaves
law open.go:
  for +s: List<&2, Tree.Frame>
  for +cc: U32
  for -r: List<&2, Lex.Tok>
  for e: {M1.vs(s) == Some{r} : Maybe<&2, List<&2, Lex.Tok>>}
  {M1.vg(Tree.FStmt{cc, Tree.NNil{}, Tree.NNil{}} <> Tree.end_n(Tree.deeper(s, cc), s)) == Some{r}
    : Maybe<&2, List<&2, Lex.Tok>>}

def open.go(s, cc, r, e):
  Equal.trans(Maybe<&2, List<&2, Lex.Tok>>,
    M1.m_stmt(M1.vs(Tree.end_n(Tree.deeper(s, cc), s)), Tree.NNil{}, Tree.NNil{}),
    M1.vs(s), Some{r},
    Equal.trans(Maybe<&2, List<&2, Lex.Tok>>,
      M1.m_stmt(M1.vs(Tree.end_n(Tree.deeper(s, cc), s)), Tree.NNil{}, Tree.NNil{}),
      M1.vs(Tree.end_n(Tree.deeper(s, cc), s)), M1.vs(s),
      m_stmt.nil(M1.vs(Tree.end_n(Tree.deeper(s, cc), s))),
      end_n(Tree.deeper(s, cc), s)),
    e)

# a line's start keeps the leaves
law open_stmt:
  for +s: List<&2, Tree.Frame>
  for +cc: U32
  for -r: List<&2, Lex.Tok>
  for e: {M1.vg(s) == Some{r} : Maybe<&2, List<&2, Lex.Tok>>}
  {M1.vg(Tree.open_stmt(s, cc)) == Some{r} : Maybe<&2, List<&2, Lex.Tok>>}

def open_stmt(s, cc, r, e):
  match s:
    case Con{Tree.FGroup{_o, _k}, _rest}:
      e
    case Con{Tree.FStmt{i, k, Tree.NNil{}}, rest}:
      open.go(Tree.FStmt{i, k, Tree.NNil{}} <> rest, cc, r, e)
    case Con{Tree.FStmt{i, k, Tree.NCons{h, t}}, rest}:
      Empty.absurd({M1.vg(Tree.open_stmt(Tree.FStmt{i, k, Tree.NCons{h, t}} <> rest, cc)) == Some{r}
        : Maybe<&2, List<&2, Lex.Tok>>}, none_some(r, e))
    case Con{Tree.FStmt{i, k, Tree.Leaf{x}}, rest}:
      Empty.absurd({M1.vg(Tree.open_stmt(Tree.FStmt{i, k, Tree.Leaf{x}} <> rest, cc)) == Some{r}
        : Maybe<&2, List<&2, Lex.Tok>>}, none_some(r, e))
    case Con{Tree.FStmt{i, k, Tree.Group{x, y, z}}, rest}:
      Empty.absurd({M1.vg(Tree.open_stmt(Tree.FStmt{i, k, Tree.Group{x, y, z}} <> rest, cc)) == Some{r}
        : Maybe<&2, List<&2, Lex.Tok>>}, none_some(r, e))
    case Con{Tree.FStmt{i, k, Tree.Stmt{x, y, z}}, rest}:
      Empty.absurd({M1.vg(Tree.open_stmt(Tree.FStmt{i, k, Tree.Stmt{x, y, z}} <> rest, cc)) == Some{r}
        : Maybe<&2, List<&2, Lex.Tok>>}, none_some(r, e))
    case Con{Tree.FRoot{b}, rest}:
      open.go(Tree.FRoot{b} <> rest, cc, r, e)
    case Nil{}:
      e

# whichever stack the cut picks, the leaves are the same
law vg.stop:
  for +b: Bool
  for -x: List<&2, Tree.Frame>
  for -f: Unit -> List<&2, Tree.Frame>
  for -z: Maybe<&2, List<&2, Lex.Tok>>
  for ex: {M1.vg(x) == z : Maybe<&2, List<&2, Lex.Tok>>}
  for ef: {M1.vg(f(Unit{})) == z : Maybe<&2, List<&2, Lex.Tok>>}
  {M1.vg(Lazy.stop(List<&2, Tree.Frame>, b, x, f)) == z : Maybe<&2, List<&2, Lex.Tok>>}

def vg.stop(b, _x, _f, _z, ex, ef):
  match b:
    case True{}:
      ex
    case False{}:
      ef

# a token that starts a line keeps the leaves
law fresh:
  for +s: List<&2, Tree.Frame>
  for +k: Lex.TokKind
  for +t: String
  for +l: U32
  for +c: U32
  for -r: List<&2, Lex.Tok>
  for +e: {M1.vg(s) == Some{r} : Maybe<&2, List<&2, Lex.Tok>>}
  {M1.vg(Tree.fresh(s, Lex.Tok{k, t, l, c})) == Some{r} : Maybe<&2, List<&2, Lex.Tok>>}

def fresh(s, _k, t, _l, c, r, e):
  open_stmt(
    Lazy.stop(List<&2, Tree.Frame>,
      Bool.not(Bool.and(Bool.and(Tree.in_group(s), U32.is_eq(c, 0)), Nat.is_eq(Tree.depth_to(s, t), 0n))),
      s, _u => Tree.close_all(s)),
    c, r,
    vg.stop(Bool.not(Bool.and(Bool.and(Tree.in_group(s), U32.is_eq(c, 0)), Nat.is_eq(Tree.depth_to(s, t), 0n))),
      s, _u => Tree.close_all(s), Some{r}, e,
      Equal.trans(Maybe<&2, List<&2, Lex.Tok>>, M1.vg(Tree.close_all(s)), M1.vg(s), Some{r}, close_all(s), e)))

# the machine's stack
def stk(st: Tree.B) -> List<&2, Tree.Frame>:
  match st:
    case Tree.B{_fr, stack}:
      stack

# trivia keeps the leaves; a significant token adds what it adds
law sig.stop:
  for +s: Bool
  for -x: Tree.B
  for -f: Unit -> Tree.B
  for -a: List<&2, Lex.Tok>
  for -r: List<&2, Lex.Tok>
  for ex: {M1.vg(stk(x)) == Some{r} : Maybe<&2, List<&2, Lex.Tok>>}
  for ef: {M1.vg(stk(f(Unit{}))) == Some{List.reverse.go(&2, Lex.Tok, a, r)} : Maybe<&2, List<&2, Lex.Tok>>}
  {M1.vg(stk(Lazy.stop(Tree.B, Bool.not(s), x, f)))
    == Some{List.reverse.go(&2, Lex.Tok, Bool.pick(List<&2, Lex.Tok>, s, a, []), r)} : Maybe<&2, List<&2, Lex.Tok>>}

def sig.stop(s, _x, _f, _a, _r, ex, ef):
  match s:
    case True{}:
      ef
    case False{}:
      ex

# the stack a significant token lands on: fresh's when it starts a line
def landing(fr: Bool, +s: List<&2, Tree.Frame>, k: Lex.TokKind, t: String, l: U32, c: U32) -> List<&2, Tree.Frame>:
  Lazy.stop(List<&2, Tree.Frame>, Bool.not(fr), s, _u2 => Tree.fresh(s, Lex.Tok{k, t, l, c}))

# a line's first token keeps the leaves
law landing.keeps:
  for +fr: Bool
  for +s: List<&2, Tree.Frame>
  for +k: Lex.TokKind
  for +t: String
  for +l: U32
  for +c: U32
  for -r: List<&2, Lex.Tok>
  for +e: {M1.vg(s) == Some{r} : Maybe<&2, List<&2, Lex.Tok>>}
  {M1.vg(landing(fr, s, k, t, l, c)) == Some{r} : Maybe<&2, List<&2, Lex.Tok>>}

def landing.keeps(fr, s, k, t, l, c, r, e):
  vg.stop(Bool.not(fr), s, _u2 => Tree.fresh(s, Lex.Tok{k, t, l, c}), Some{r}, e, fresh(s, k, t, l, c, r, e))

# one step adds the token's leaves
law tstep:
  for +k: Lex.TokKind
  for +t: String
  for +l: U32
  for +c: U32
  for +st: Tree.B
  for +g: Bool
  for -r: List<&2, Lex.Tok>
  for +e: {M1.vg(stk(st)) == Some{r} : Maybe<&2, List<&2, Lex.Tok>>}
  {M1.vg(stk(Tree.step(Lex.Tok{k, t, l, c}, st, g))) == Some{List.reverse.go(&2, Lex.Tok, M1.adds(k, t, l, c), r)}
    : Maybe<&2, List<&2, Lex.Tok>>}

def tstep(k, t, l, c, st, g, r, e):
  match st:
    case Tree.B{fr, s}:
      sig.stop(Lex.significant(k), Tree.B{Bool.or(fr, Lex.is_nl(k)), s},
        _u => Tree.B{False{}, Tree.push(landing(fr, s, k, t, l, c), Lex.Tok{k, t, l, c}, g)},
        M1.law_adds(k, t, l, c), r, e,
        Equal.trans(Maybe<&2, List<&2, Lex.Tok>>,
          M1.vg(Tree.push(landing(fr, s, k, t, l, c), Lex.Tok{k, t, l, c}, g)),
          m_toks(M1.vg(landing(fr, s, k, t, l, c)), code_adds(k, t, l, c)),
          Some{List.reverse.go(&2, Lex.Tok, M1.law_adds(k, t, l, c), r)},
          push(landing(fr, s, k, t, l, c), k, t, l, c, g),
          Equal.trans(Maybe<&2, List<&2, Lex.Tok>>,
            m_toks(M1.vg(landing(fr, s, k, t, l, c)), code_adds(k, t, l, c)),
            Some{List.reverse.go(&2, Lex.Tok, code_adds(k, t, l, c), r)},
            Some{List.reverse.go(&2, Lex.Tok, M1.law_adds(k, t, l, c), r)},
            Equal.cong(Maybe<&2, List<&2, Lex.Tok>>, Maybe<&2, List<&2, Lex.Tok>>,
              m => m_toks(m, code_adds(k, t, l, c)),
              M1.vg(landing(fr, s, k, t, l, c)), Some{r},
              landing.keeps(fr, s, k, t, l, c, r, e)),
            Equal.cong(List<&2, Lex.Tok>, Maybe<&2, List<&2, Lex.Tok>>,
              x => Some{List.reverse.go(&2, Lex.Tok, x, r)},
              code_adds(k, t, l, c), M1.law_adds(k, t, l, c), decide(k, t, l, c)))))

# one less
def pred(nn: Nat) -> Nat:
  match nn:
    case Zero{}:
      0n
    case Succ{p}:
      p

# a known list's value, [] for none
def got(mm: Maybe<&2, List<&2, Lex.Tok>>) -> List<&2, Lex.Tok>:
  match mm:
    case None{}:
      []
    case Some{a}:
      a

# a put keeps the groups on top
law groups.put:
  for +s: List<&2, Tree.Frame>
  for +x: Tree.Node
  {Tree.groups(Tree.put(s, x)) == Tree.groups(s) : Nat}

def groups.put(s, _x):
  match s:
    case Con{Tree.FGroup{_o, _k}, _rest}:
      {==}
    case Con{Tree.FStmt{_i, _k, _b}, _rest}:
      {==}
    case Con{Tree.FRoot{_b}, _rest}:
      {==}
    case Nil{}:
      {==}

# a statement put in a body keeps the statements on top
law stmts.put:
  for +s: List<&2, Tree.Frame>
  for +x: Tree.Node
  {Tree.stmts(Tree.put_stmt(s, x)) == Tree.stmts(s) : Nat}

def stmts.put(s, _x):
  match s:
    case Con{Tree.FGroup{_o, _k}, _rest}:
      {==}
    case Con{Tree.FStmt{_i, _k, _b}, _rest}:
      {==}
    case Con{Tree.FRoot{_b}, _rest}:
      {==}
    case Nil{}:
      {==}

# with no group on top, a well-formed stack's leaves are its statements'
law no_group:
  for +s: List<&2, Tree.Frame>
  for -r: List<&2, Lex.Tok>
  for eg: {Tree.groups(s) == 0n : Nat}
  for ev: {M1.vg(s) == Some{r} : Maybe<&2, List<&2, Lex.Tok>>}
  {M1.vs(s) == Some{r} : Maybe<&2, List<&2, Lex.Tok>>}

def no_group(s, r, eg, ev):
  match s:
    case Con{Tree.FGroup{o, k}, rest}:
      Empty.absurd({M1.vs(Tree.FGroup{o, k} <> rest) == Some{r} : Maybe<&2, List<&2, Lex.Tok>>},
        zero_succ(Tree.groups(rest), Equal.sym(Nat, 1n+Tree.groups(rest), 0n, eg)))
    case Con{Tree.FStmt{_i, _k, Tree.NNil{}}, _rest}:
      ev
    case Con{Tree.FStmt{i, k, Tree.NCons{h, t}}, rest}:
      Empty.absurd({M1.vs(Tree.FStmt{i, k, Tree.NCons{h, t}} <> rest) == Some{r} : Maybe<&2, List<&2, Lex.Tok>>},
        none_some(r, ev))
    case Con{Tree.FStmt{i, k, Tree.Leaf{x}}, rest}:
      Empty.absurd({M1.vs(Tree.FStmt{i, k, Tree.Leaf{x}} <> rest) == Some{r} : Maybe<&2, List<&2, Lex.Tok>>},
        none_some(r, ev))
    case Con{Tree.FStmt{i, k, Tree.Group{x, y, z}}, rest}:
      Empty.absurd({M1.vs(Tree.FStmt{i, k, Tree.Group{x, y, z}} <> rest) == Some{r} : Maybe<&2, List<&2, Lex.Tok>>},
        none_some(r, ev))
    case Con{Tree.FStmt{i, k, Tree.Stmt{x, y, z}}, rest}:
      Empty.absurd({M1.vs(Tree.FStmt{i, k, Tree.Stmt{x, y, z}} <> rest) == Some{r} : Maybe<&2, List<&2, Lex.Tok>>},
        none_some(r, ev))
    case Con{Tree.FRoot{_b}, _rest}:
      ev
    case Nil{}:
      ev

# closing the n groups on top leaves a stack whose statements hold the leaves
law close_down:
  for +n: Nat
  for +s: List<&2, Tree.Frame>
  for -r: List<&2, Lex.Tok>
  for eg: {Tree.groups(s) == n : Nat}
  for ev: {M1.vg(s) == Some{r} : Maybe<&2, List<&2, Lex.Tok>>}
  {M1.vs(Tree.close_n(n, s, None{})) == Some{r} : Maybe<&2, List<&2, Lex.Tok>>}

def close_down(n, s, r, eg, ev):
  match n s:
    case Zero{} _s:
      no_group(_s, r, eg, ev)
    case Succ{Zero{}} Con{Tree.FGroup{o, k}, rest}:
      no_group(Tree.put(rest, Tree.Group{o, Tree.reverse(k, Tree.NNil{}), None{}}), r,
        Equal.trans(Nat, Tree.groups(Tree.put(rest, Tree.Group{o, Tree.reverse(k, Tree.NNil{}), None{}})),
          Tree.groups(rest), 0n,
          groups.put(rest, Tree.Group{o, Tree.reverse(k, Tree.NNil{}), None{}}),
          Equal.cong(Nat, Nat, pred, 1n+Tree.groups(rest), 1n, eg)),
        Equal.trans(Maybe<&2, List<&2, Lex.Tok>>,
          M1.vg(Tree.close_one(Tree.FGroup{o, k} <> rest, None{})), M1.vg(Tree.FGroup{o, k} <> rest), Some{r},
          close.none(Tree.FGroup{o, k} <> rest), ev))
    case Succ{Succ{q}} Con{Tree.FGroup{o, k}, rest}:
      close_down(1n+q, Tree.put(rest, Tree.Group{o, Tree.reverse(k, Tree.NNil{}), None{}}), r,
        Equal.trans(Nat, Tree.groups(Tree.put(rest, Tree.Group{o, Tree.reverse(k, Tree.NNil{}), None{}})),
          Tree.groups(rest), 1n+q,
          groups.put(rest, Tree.Group{o, Tree.reverse(k, Tree.NNil{}), None{}}),
          Equal.cong(Nat, Nat, pred, 1n+Tree.groups(rest), 1n+1n+q, eg)),
        Equal.trans(Maybe<&2, List<&2, Lex.Tok>>,
          M1.vg(Tree.close_one(Tree.FGroup{o, k} <> rest, None{})), M1.vg(Tree.FGroup{o, k} <> rest), Some{r},
          close.none(Tree.FGroup{o, k} <> rest), ev))
    case Succ{p} Con{Tree.FStmt{i, k, b}, rest}:
      Empty.absurd({M1.vs(Tree.close_n(1n+p, Tree.FStmt{i, k, b} <> rest, None{})) == Some{r}
        : Maybe<&2, List<&2, Lex.Tok>>},
        zero_succ(p, eg))
    case Succ{p} Con{Tree.FRoot{b}, rest}:
      Empty.absurd({M1.vs(Tree.close_n(1n+p, Tree.FRoot{b} <> rest, None{})) == Some{r} : Maybe<&2, List<&2, Lex.Tok>>},
        zero_succ(p, eg))
    case Succ{p} Nil{}:
      Empty.absurd({M1.vs(Tree.close_n(1n+p, [], None{})) == Some{r} : Maybe<&2, List<&2, Lex.Tok>>},
        zero_succ(p, eg))

# finishing the n statements on top leaves the root, whose items read back
# the leaves in order
law end_down:
  for +n: Nat
  for +s: List<&2, Tree.Frame>
  for -r: List<&2, Lex.Tok>
  for es: {Tree.stmts(s) == n : Nat}
  for ev: {M1.vs(s) == Some{r} : Maybe<&2, List<&2, Lex.Tok>>}
  {Tree.leaves(Tree.root(Tree.end_n(n, s))) == List.reverse(&2, Lex.Tok, r) : List<&2, Lex.Tok>}

def end_down(n, s, r, es, ev):
  match n s:
    case Zero{} Con{Tree.FRoot{b}, _rest}:
      Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, x => List.reverse(&2, Lex.Tok, x),
        Tree.leaves.go(Tree.reverse(b, Tree.NNil{}), []), r,
        Equal.trans(List<&2, Lex.Tok>, Tree.leaves.go(Tree.reverse(b, Tree.NNil{}), []), M1.rgo(b, []), r,
          rev(b, Tree.NNil{}, []),
          Equal.cong(Maybe<&2, List<&2, Lex.Tok>>, List<&2, Lex.Tok>, got, Some{M1.rgo(b, [])}, Some{r}, ev)))
    case Zero{} Con{Tree.FStmt{i, k, b}, rest}:
      Empty.absurd({Tree.leaves(Tree.root(Tree.end_n(0n, Tree.FStmt{i, k, b} <> rest))) == List.reverse(&2, Lex.Tok, r)
        : List<&2, Lex.Tok>},
        zero_succ(Tree.stmts(rest), Equal.sym(Nat, 1n+Tree.stmts(rest), 0n, es)))
    case Zero{} Con{Tree.FGroup{o, k}, rest}:
      Empty.absurd({Tree.leaves(Tree.root(Tree.end_n(0n, Tree.FGroup{o, k} <> rest))) == List.reverse(&2, Lex.Tok, r)
        : List<&2, Lex.Tok>},
        none_some(r, ev))
    case Zero{} Nil{}:
      Empty.absurd({Tree.leaves(Tree.root(Tree.end_n(0n, []))) == List.reverse(&2, Lex.Tok, r) : List<&2, Lex.Tok>},
        none_some(r, ev))
    case Succ{p} Con{Tree.FStmt{i, k, b}, rest}:
      end_down(p, Tree.end_stmt(Tree.FStmt{i, k, b} <> rest), r,
        Equal.trans(Nat, Tree.stmts(Tree.end_stmt(Tree.FStmt{i, k, b} <> rest)), Tree.stmts(rest), p,
          stmts.put(rest, Tree.Stmt{Tree.classify(Tree.reverse(k, Tree.NNil{})), Tree.reverse(k, Tree.NNil{}),
            Tree.reverse(b, Tree.NNil{})}),
          Equal.cong(Nat, Nat, pred, 1n+Tree.stmts(rest), 1n+p, es)),
        Equal.trans(Maybe<&2, List<&2, Lex.Tok>>,
          M1.vs(Tree.end_stmt(Tree.FStmt{i, k, b} <> rest)), M1.vs(Tree.FStmt{i, k, b} <> rest), Some{r},
          end_stmt(Tree.FStmt{i, k, b} <> rest), ev))
    case Succ{p} Con{Tree.FGroup{o, k}, rest}:
      Empty.absurd({Tree.leaves(Tree.root(Tree.end_n(1n+p, Tree.FGroup{o, k} <> rest))) == List.reverse(&2, Lex.Tok, r)
        : List<&2, Lex.Tok>},
        zero_succ(p, es))
    case Succ{p} Con{Tree.FRoot{b}, rest}:
      Empty.absurd({Tree.leaves(Tree.root(Tree.end_n(1n+p, Tree.FRoot{b} <> rest))) == List.reverse(&2, Lex.Tok, r)
        : List<&2, Lex.Tok>},
        zero_succ(p, es))
    case Succ{p} Nil{}:
      Empty.absurd({Tree.leaves(Tree.root(Tree.end_n(1n+p, []))) == List.reverse(&2, Lex.Tok, r) : List<&2, Lex.Tok>},
        zero_succ(p, es))

# the finished tree reads back the leaves in order
law tfinish:
  for +st: Tree.B
  for -r: List<&2, Lex.Tok>
  for e: {M1.vg(stk(st)) == Some{r} : Maybe<&2, List<&2, Lex.Tok>>}
  {Tree.leaves(Tree.finish(st)) == List.reverse(&2, Lex.Tok, r) : List<&2, Lex.Tok>}

def tfinish(st, r, e):
  match st:
    case Tree.B{_fr, s}:
      end_down(Tree.stmts(Tree.close_all(s)), Tree.close_all(s), r, {==},
        close_down(Tree.groups(s), s, r, {==}, e))

# a list reversed onto a list reversed onto another
law rev_rev:
  for +xs: List<&2, Lex.Tok>
  for +r: List<&2, Lex.Tok>
  for +ys: List<&2, Lex.Tok>
  {List.reverse.go(&2, Lex.Tok, List.reverse.go(&2, Lex.Tok, xs, r), ys)
    == List.reverse.go(&2, Lex.Tok, r, List.append(&2, Lex.Tok, xs, ys)) : List<&2, Lex.Tok>}

def rev_rev(xs, r, ys):
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      rev_rev(t, h <> r, ys)

# one token's leaves, then the rest's: the law's leaves of both
law split_one:
  for +s: Bool
  for +k: Lex.TokKind
  for +t: String
  for +l: U32
  for +c: U32
  for +more: List<&2, Lex.Tok>
  {List.append(&2, Lex.Tok,
      Bool.pick(List<&2, Lex.Tok>, s,
        M1.law_adds(k, t, l, c), []),
      Laws.split_gts(more))
    == Laws.split_gts(Bool.pick(List<&2, Lex.Tok>, s, Lex.Tok{k, t, l, c} <> more, more)) : List<&2, Lex.Tok>}

def split_one(s, _k, _t, _l, _c, _more):
  match s:
    case True{}:
      {==}
    case False{}:
      {==}

# running over tokens adds their leaves, and the finished tree reads all of
# them back in order
law trun:
  for +toks: List<&2, Lex.Tok>
  for +st: Tree.B
  for +g: Bool
  for +r: List<&2, Lex.Tok>
  for +e: {M1.vg(stk(st)) == Some{r} : Maybe<&2, List<&2, Lex.Tok>>}
  {Tree.leaves(Tree.finish(Tree.run(toks, st, g)))
    == List.reverse.go(&2, Lex.Tok, r, Laws.split_gts(Laws.significant(toks))) : List<&2, Lex.Tok>}

def trun(toks, st, g, r, e):
  match toks:
    case Nil{}:
      tfinish(st, r, e)
    case Con{Lex.Tok{k, t, l, c}, rest}:
      Equal.trans(List<&2, Lex.Tok>,
        Tree.leaves(Tree.finish(Tree.run(rest, Tree.step(Lex.Tok{k, t, l, c}, st, g),
          Tree.is_name_tok(Lex.Tok{k, t, l, c})))),
        List.reverse.go(&2, Lex.Tok, List.reverse.go(&2, Lex.Tok, M1.adds(k, t, l, c), r),
          Laws.split_gts(Laws.significant(rest))),
        List.reverse.go(&2, Lex.Tok, r, Laws.split_gts(Laws.significant(Lex.Tok{k, t, l, c} <> rest))),
        trun(rest, Tree.step(Lex.Tok{k, t, l, c}, st, g), Tree.is_name_tok(Lex.Tok{k, t, l, c}),
          List.reverse.go(&2, Lex.Tok, M1.adds(k, t, l, c), r), tstep(k, t, l, c, st, g, r, e)),
        Equal.trans(List<&2, Lex.Tok>,
          List.reverse.go(&2, Lex.Tok, List.reverse.go(&2, Lex.Tok, M1.adds(k, t, l, c), r),
            Laws.split_gts(Laws.significant(rest))),
          List.reverse.go(&2, Lex.Tok, r, List.append(&2, Lex.Tok, M1.adds(k, t, l, c),
            Laws.split_gts(Laws.significant(rest)))),
          List.reverse.go(&2, Lex.Tok, r, Laws.split_gts(Laws.significant(Lex.Tok{k, t, l, c} <> rest))),
          rev_rev(M1.adds(k, t, l, c), r, Laws.split_gts(Laws.significant(rest))),
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, x => List.reverse.go(&2, Lex.Tok, r, x),
            List.append(&2, Lex.Tok, M1.adds(k, t, l, c), Laws.split_gts(Laws.significant(rest))),
            Laws.split_gts(Laws.significant(Lex.Tok{k, t, l, c} <> rest)),
            split_one(Lex.significant(k), k, t, l, c, Laws.significant(rest)))))

def Laws.leaves(toks):
  trun(toks, Tree.B{True{}, [Tree.FRoot{Tree.NNil{}}]}, False{}, [], {==})
