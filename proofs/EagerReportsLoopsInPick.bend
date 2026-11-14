# proofs of laws/EagerReportsLoopsInPick.bend
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/lazy/lazy.bend as Lazy
import ../src/syntax/tree.bend as Tree
import ../src/rules/calls.bend as Calls
import ../src/rules/correctness/pick.bend as Pick
import ../src/rules/suspicious/eager.bend as Eager
import ../laws/EagerReportsLoopsInPick.bend as Laws
import ./lemmas/ConcatSums.bend as M1
import ./lemmas/Nat.bend as M2
import ./lemmas/Pick.bend as M3
import ./lemmas/LoopSetIndex.bend as LP

# eager (laws/EagerReportsLoopsInPick.bend). The walk reports a hot call in front of its
# group's findings and the rest's, so the count adds one before adding
# them; the def walk is concat's, so concat's lemmas carry it.

# work finds what the law's count counts, node by node, in every state
law eager.work:
  for n: Tree.Node
  for +ns: List<&2, String>
  for +self: String
  for +path: String
  for +hot: Bool
  for +seg: U32
  for +keep: Bool
  {List.length(&2, F.Finding, Eager.work(n, ns, self, path, hot, seg, keep))
    == Laws.eager.count(n, ns, self, hot, seg, keep) : Nat}

def eager.work(n, ns, self, path, hot, seg, keep):
  match n:
    case Tree.NCons{Tree.Leaf{Lex.Tok{+k, +t, +l, +c}}, Tree.NCons{Tree.Group{Lex.Tok{_, +o, _, _}, +kids, _}, +rest}}:
      +now = Eager.work.hot(k, hot, seg, keep)
      +call = Bool.and(Eager.work.name(k), String.eq(o, "("))
      +is_pick = Bool.and(call, String.eq(t, "Bool.pick"))
      +mine = Bool.and(Bool.not(String.eq(t, self)), List.contains(~String, ~String.eq, ns, t))
      +inner = Bool.and(now, Bool.not(is_pick))
      M2.nat.pick(Bool.and(now, Bool.and(call, mine)),
        F.Finding{path, l, c, U32.from_nat(String.length(t)), "eager",
          t ++ " is called in a branch of Bool.pick, which evaluates both branches, so it runs whatever the condition; bind it above the pick, or branch with `match` on the condition."},
        List.concat(&2, F.Finding,
          [Eager.work(kids, ns, self, path, inner, Bool.pick(U32, is_pick, 0, 9), inner),
            Eager.work(rest, ns, self, path, now, Eager.work.seg(k, seg), keep)]),
        Nat.add(Laws.eager.count(kids, ns, self, inner, Bool.pick(U32, is_pick, 0, 9), inner),
          Laws.eager.count(rest, ns, self, now, Eager.work.seg(k, seg), keep)),
        M1.concat.two(Eager.work(kids, ns, self, path, inner, Bool.pick(U32, is_pick, 0, 9), inner),
          Eager.work(rest, ns, self, path, now, Eager.work.seg(k, seg), keep),
          Laws.eager.count(kids, ns, self, inner, Bool.pick(U32, is_pick, 0, 9), inner),
          Laws.eager.count(rest, ns, self, now, Eager.work.seg(k, seg), keep),
          eager.work(kids, ns, self, path, inner, Bool.pick(U32, is_pick, 0, 9), inner),
          eager.work(rest, ns, self, path, now, Eager.work.seg(k, seg), keep)))
    case Tree.NCons{Tree.Leaf{Lex.Tok{+k, t, l, c}}, Tree.NCons{Tree.Leaf{x}, rest}}:
      eager.work(Tree.NCons{Tree.Leaf{x}, rest}, ns, self, path, Eager.work.hot(k, hot, seg, keep),
        Eager.work.seg(k, seg), keep)
    case Tree.NCons{Tree.Leaf{Lex.Tok{+k, t, l, c}}, Tree.NCons{Tree.Stmt{kind, kids, body}, rest}}:
      eager.work(Tree.NCons{Tree.Stmt{kind, kids, body}, rest}, ns, self, path, Eager.work.hot(k, hot, seg, keep),
        Eager.work.seg(k, seg), keep)
    case Tree.NCons{Tree.Leaf{Lex.Tok{+k, t, l, c}}, Tree.NCons{Tree.NNil{}, rest}}:
      eager.work(Tree.NCons{Tree.NNil{}, rest}, ns, self, path, Eager.work.hot(k, hot, seg, keep),
        Eager.work.seg(k, seg), keep)
    case Tree.NCons{Tree.Leaf{Lex.Tok{+k, t, l, c}}, Tree.NCons{Tree.NCons{a, b}, rest}}:
      eager.work(Tree.NCons{Tree.NCons{a, b}, rest}, ns, self, path, Eager.work.hot(k, hot, seg, keep),
        Eager.work.seg(k, seg), keep)
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}}, Tree.Leaf{x}}:
      {==}
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}}, Tree.Group{open, kids, close}}:
      {==}
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}}, Tree.Stmt{kind, kids, body}}:
      {==}
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}}, Tree.NNil{}}:
      {==}
    case Tree.NCons{Tree.Group{open, +kids, close}, +rest}:
      M1.concat.two(Eager.work(kids, ns, self, path, hot, 9, hot), Eager.work(rest, ns, self, path, hot, seg, keep),
        Laws.eager.count(kids, ns, self, hot, 9, hot), Laws.eager.count(rest, ns, self, hot, seg, keep),
        eager.work(kids, ns, self, path, hot, 9, hot), eager.work(rest, ns, self, path, hot, seg, keep))
    case Tree.NCons{Tree.Stmt{kind, +kids, +body}, +rest}:
      M1.concat.three(Eager.work(kids, ns, self, path, False{}, 9, False{}),
        Eager.work(body, ns, self, path, False{}, 9, False{}), Eager.work(rest, ns, self, path, hot, seg, keep),
        Laws.eager.count(kids, ns, self, False{}, 9, False{}), Laws.eager.count(body, ns, self, False{}, 9, False{}),
        Laws.eager.count(rest, ns, self, hot, seg, keep),
        eager.work(kids, ns, self, path, False{}, 9, False{}), eager.work(body, ns, self, path, False{}, 9, False{}),
        eager.work(rest, ns, self, path, hot, seg, keep))
    case Tree.NCons{Tree.NNil{}, rest}:
      eager.work(rest, ns, self, path, hot, seg, keep)
    case Tree.NCons{Tree.NCons{a, b}, rest}:
      eager.work(rest, ns, self, path, hot, seg, keep)
    case Tree.Leaf{x}:
      {==}
    case Tree.Group{open, kids, close}:
      {==}
    case Tree.Stmt{kind, kids, body}:
      {==}
    case Tree.NNil{}:
      {==}

# the def walk adds each def's count, none for an exempt def, to what its
# accumulator already holds
law eager.go:
  for ds: List<&2, Calls.Def>
  for +ns: List<&2, String>
  for +path: String
  for +acc: List<&2, List<&2, F.Finding>>
  {List.length(&2, F.Finding, Eager.check.go(ds, ns, path, acc))
    == Nat.add(M1.concat.sum(acc), Laws.eager.file(ds, ns, path)) : Nat}

def eager.go(ds, ns, path, acc):
  match ds:
    case Nil{}:
      Equal.trans(Nat,
        List.length(&2, F.Finding, List.concat(&2, F.Finding, List.reverse(&2, List<&2, F.Finding>, acc))),
        M1.concat.sum(List.reverse.go(&2, List<&2, F.Finding>, acc, Nil{})), Nat.add(M1.concat.sum(acc), 0n),
        M1.concat.flat(List.reverse(&2, List<&2, F.Finding>, acc)), M1.concat.rsum(acc, Nil{}))
    case Con{Calls.Def{+name, +sig, +body}, +rest}:
      Equal.trans(Nat,
        List.length(&2, F.Finding, Eager.check.go(rest, ns, path,
          Lazy.stop(List<&2, F.Finding>, Calls.exempt(path, sig), [],
            _u => Eager.work(body, ns, name, path, False{}, 9, False{})) <> acc)),
        Nat.add(Nat.add(List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, Calls.exempt(path, sig), [],
          _u => Eager.work(body, ns, name, path, False{}, 9, False{}))), M1.concat.sum(acc)),
          Laws.eager.file(rest, ns, path)),
        Nat.add(M1.concat.sum(acc),
          Nat.add(Bool.pick(Nat, Calls.exempt(path, sig), 0n, Laws.eager.count(body, ns, name, False{}, 9, False{})),
            Laws.eager.file(rest, ns, path))),
        eager.go(rest, ns, path, Lazy.stop(List<&2, F.Finding>, Calls.exempt(path, sig), [],
          _u => Eager.work(body, ns, name, path, False{}, 9, False{})) <> acc),
        M1.concat.move(List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, Calls.exempt(path, sig), [],
            _u => Eager.work(body, ns, name, path, False{}, 9, False{}))),
          Bool.pick(Nat, Calls.exempt(path, sig), 0n, Laws.eager.count(body, ns, name, False{}, 9, False{})),
          M1.concat.sum(acc), Laws.eager.file(rest, ns, path),
          M3.param.stop(Calls.exempt(path, sig), Eager.work(body, ns, name, path, False{}, 9, False{}),
            Laws.eager.count(body, ns, name, False{}, 9, False{}),
            eager.work(body, ns, name, path, False{}, 9, False{}))))

def Laws.eager_counts(path, _text, _toks, tree, _bound, _items):
  eager.go(Calls.defs(tree), Eager.loops(Calls.defs(tree)), path, [])

def Laws.eager_lambda(_hot, _seg, _keep):
  {==}

def Laws.eager_comma(_hot, _keep):
  {==}

# Unit for False, Empty for True
def eager.false_ty(b: Bool) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      Empty

# False is never True
law eager.false_true:
  for e: {False{} == True{} : Bool}
  Empty

def eager.false_true(e):
  %e : eager.false_ty(_)
  Unit{}

def Laws.eager_plain(k, hot, seg, keep, e):
  match k:
    case Lex.TLam{}:
      Empty.absurd(
        {(Eager.work.hot(Lex.TLam{}, hot, seg, keep), Eager.work.seg(Lex.TLam{}, seg), Eager.work.name(Lex.TLam{}))
          == (hot, seg, True{}) : Bool & U32 & Bool}, eager.false_true(e))
    case Lex.TComma{}:
      Empty.absurd(
        {(Eager.work.hot(Lex.TComma{}, hot, seg, keep), Eager.work.seg(Lex.TComma{}, seg),
            Eager.work.name(Lex.TComma{}))
          == (hot, seg, True{}) : Bool & U32 & Bool}, eager.false_true(e))
    case Lex.TName{}:
      {==}
    case Lex.TUpper{}:
      {==}
    case Lex.TDotted{}:
      {==}
    case Lex.TWild{}:
      {==}
    case Lex.TKey{}:
      {==}
    case Lex.TNum{}:
      {==}
    case Lex.TStr{}:
      {==}
    case Lex.TChar{}:
      {==}
    case Lex.TComment{}:
      {==}
    case Lex.TSpace{}:
      {==}
    case Lex.TNewline{}:
      {==}
    case Lex.TOp{}:
      {==}
    case Lex.TColon{}:
      {==}
    case Lex.TEq{}:
      {==}
    case Lex.TBind{}:
      {==}
    case Lex.TArrow{}:
      {==}
    case Lex.TAll{}:
      {==}
    case Lex.TAmp{}:
      {==}
    case Lex.TOpen{}:
      {==}
    case Lex.TClose{}:
      {==}

# a lazy or is the plain or, the rest of the search being the law's
law eager.or_else:
  for b: Bool
  for -x: Bool
  for -y: Bool
  for ih: {x == y : Bool}
  {Lazy.or_else(b, _u => x) == Bool.or(b, y) : Bool}

def eager.or_else(b, _x, _y, ih):
  match b:
    case True{}:
      {==}
    case False{}:
      ih

# the rule's search of the set is the law's
law eager.any_eq:
  for cs: List<&2, String>
  for +set: List<&2, String>
  {Eager.loops.any(cs, set) == Laws.eager.any(cs, set) : Bool}

def eager.any_eq(cs, set):
  match cs:
    case Nil{}:
      {==}
    case Con{+c, +t}:
      eager.or_else(List.contains(~String, ~String.eq, set, c), Eager.loops.any(t, set), Laws.eager.any(t, set),
        eager.any_eq(t, set))

# the rule's walk that carries the names gathers the law's looping defs
law eager.loops_eq:
  for ds: List<&2, Calls.Def>
  for +acc: List<&2, String>
  {Eager.loops.go(ds, acc) == Laws.eager.loops(ds, acc) : List<&2, String>}

def eager.loops_eq(ds, acc):
  match ds:
    case Nil{}:
      {==}
    case Con{Calls.Def{+name, +sig, +body}, +rest}:
      +cs = Eager.called(body)
      +self = List.contains(~String, ~String.eq, cs, name)
      %eager.any_eq(cs, acc) :
        {Eager.loops.go(Calls.Def{name, sig, body} <> rest, acc)
          == Laws.eager.loops(rest, Bool.pick(List<&2, String>, Bool.or(self, _), name <> acc, acc))
          : List<&2, String>}
      eager.loops_eq(rest, Bool.pick(List<&2, String>, Bool.or(self, Eager.loops.any(cs, acc)), name <> acc, acc))

def Laws.eager_loops_named(ds):
  Equal.trans(List<&2, String>, Eager.loops(ds), Eager.loops.go(ds, []), Laws.eager.loops(ds, []),
    LP.lp.eager.all(ds), eager.loops_eq(ds, []))
