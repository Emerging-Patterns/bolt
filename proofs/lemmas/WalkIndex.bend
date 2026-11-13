# the import walk's indexes answer as the scans do
import Base
import ../../src/rules/imports.bend as Imports
import ../../src/syntax/bind.bend as Bind
import ../../src/lazy/lazy.bend as Lazy
import ../../laws/BinderIndexFindsItems.bend as L1
import ./BinderIndex.bend as M1
import ./InertTextFacts.bend as M2
import ./RoleProofPicked.bend as M3
import ./BinderIndexIsContains.bend as M4

# The indexes (src/rules/imports.bend). The edges go down the low bits of
# each path's number as the World's replies do (proofs/lemmas/ReplyIndex.bend
# has the same argument); the files seen and read are in the binder's index,
# whose lookup is its scan (laws/BinderIndexFindsItems.bend).

# one level of the edge index: a lookup that goes down bit b2 past a put that
# went down bit b1 reads the put's half when the bits agree and the half the
# put left alone when they do not
law wi.step:
  for b1: Bool
  for b2: Bool
  for -sub: Imports.EIx
  for -tt: Imports.EIx
  for -rest: Bool
  for -ee: Imports.Edge
  for -hs: Imports.EIx -> List<&2, Imports.Edge>
  for ih: {hs(sub)
    == Bool.pick(List<&2, Imports.Edge>, rest, ee <> hs(Imports.edges.ix.near(b1, tt)),
      hs(Imports.edges.ix.near(b1, tt))) : List<&2, Imports.Edge>}
  {hs(Imports.edges.ix.near(b2, Imports.edges.ix.join(b1, sub, Imports.edges.ix.near(Bool.not(b1), tt))))
    == Bool.pick(List<&2, Imports.Edge>, Bool.and(M1.ix.bit(b1, b2), rest), ee <> hs(Imports.edges.ix.near(b2, tt)),
      hs(Imports.edges.ix.near(b2, tt))) : List<&2, Imports.Edge>}

def wi.step(b1, b2, _sub, _tt, _rest, _ee, _hs, ih):
  match b1 b2:
    case True{} True{}:
      ih
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      ih

# a lookup after a put: the edge put in, at the front, when the two numbers
# agree in the bits walked, and what was there before
law wi.put:
  for dd: Nat
  for +k1: U32
  for +k2: U32
  for +tt: Imports.EIx
  for +ee: Imports.Edge
  {Imports.edges.ix.at(dd, k2, Imports.edges.ix.put(dd, k1, tt, ee))
    == Bool.pick(List<&2, Imports.Edge>, M1.ix.bits(dd, k1, k2), ee <> Imports.edges.ix.at(dd, k2, tt),
      Imports.edges.ix.at(dd, k2, tt)) : List<&2, Imports.Edge>}

def wi.put(dd, k1, k2, tt, ee):
  match dd:
    case 0n:
      {==}
    case 1n+p:
      wi.step(U32.is_even(k1), U32.is_even(k2),
        Imports.edges.ix.put(p, U32.shr(k1), Imports.edges.ix.near(U32.is_even(k1), tt), ee), tt,
        M1.ix.bits(p, U32.shr(k1), U32.shr(k2)), ee,
        x => Imports.edges.ix.at(p, U32.shr(k2), x),
        wi.put(p, U32.shr(k1), U32.shr(k2), Imports.edges.ix.near(U32.is_even(k1), tt), ee))

# two paths that compare equal have numbers alike in every bit walked
law wi.alike:
  for +ep: String
  for +pp: String
  for e: {String.eq(ep, pp) == True{} : Bool}
  {M1.ix.bits(Bind.index.depth(), Bind.key(ep), Bind.key(pp)) == True{} : Bool}

def wi.alike(ep, pp, e):
  %M3.unsafe.seq(ep, pp, e) : {M1.ix.bits(Bind.index.depth(), Bind.key(ep), Bind.key(_)) == True{} : Bool}
  M1.ix.bits_refl(Bind.index.depth(), Bind.key(ep))

# a test that cannot hold leaves a stop to its rest
law wi.miss:
  for ss: Bool
  for -yes: List<&2, String>
  for -no: List<&2, String>
  for imp: {ss == True{} : Bool} -> Empty
  {no == Lazy.stop(List<&2, String>, ss, yes, _u => no) : List<&2, String>}

def wi.miss(ss, yes, no, imp):
  match ss:
    case True{}:
      Empty.absurd({no == Lazy.stop(List<&2, String>, True{}, yes, _u => no) : List<&2, String>}, imp({==}))
    case False{}:
      {==}

# a leaf that may hold the edge: the search of it is the search with the edge
# first, since an edge it leaves out is one the search passes
law wi.leaf:
  for bb: Bool
  for +pp: String
  for +ep: String
  for +ds: List<&2, String>
  for +more: List<&2, Imports.Edge>
  for imp: {String.eq(ep, pp) == True{} : Bool} -> {bb == True{} : Bool}
  {Imports.deps.first(Bool.pick(List<&2, Imports.Edge>, bb, Imports.Edge{ep, ds} <> more, more), pp)
    == Imports.deps.first(Imports.Edge{ep, ds} <> more, pp) : List<&2, String>}

def wi.leaf(bb, pp, ep, ds, more, imp):
  match bb:
    case True{}:
      {==}
    case False{}:
      wi.miss(String.eq(ep, pp), ds, Imports.deps.first(more, pp), e => M2.inert.false_true(imp(e)))

# what a file imports, off the edge index, is the search of the edges
law wi.deps:
  for es: List<&2, Imports.Edge>
  for +pp: String
  {Imports.deps.ix(Imports.edges.ix.of(es), pp) == Imports.deps.first(es, pp) : List<&2, String>}

def wi.deps(es, pp):
  match es:
    case Nil{}:
      {==}
    case Con{Imports.Edge{+ep, +ds}, +rest}:
      +at = Imports.edges.ix.at(Bind.index.depth(), Bind.key(pp), Imports.edges.ix.of(rest))
      %Equal.sym(List<&2, Imports.Edge>,
        Imports.edges.ix.at(Bind.index.depth(), Bind.key(pp),
          Imports.edges.ix.put(Bind.index.depth(), Bind.key(ep), Imports.edges.ix.of(rest), Imports.Edge{ep, ds})),
        Bool.pick(List<&2, Imports.Edge>, M1.ix.bits(Bind.index.depth(), Bind.key(ep), Bind.key(pp)),
          Imports.Edge{ep, ds} <> at, at),
        wi.put(Bind.index.depth(), Bind.key(ep), Bind.key(pp), Imports.edges.ix.of(rest), Imports.Edge{ep, ds})) :
        {Imports.deps.first(_, pp) == Imports.deps.first(Imports.Edge{ep, ds} <> rest, pp) : List<&2, String>}
      %Equal.sym(List<&2, String>,
        Imports.deps.first(Bool.pick(List<&2, Imports.Edge>, M1.ix.bits(Bind.index.depth(), Bind.key(ep), Bind.key(pp)),
          Imports.Edge{ep, ds} <> at, at), pp),
        Imports.deps.first(Imports.Edge{ep, ds} <> at, pp),
        wi.leaf(M1.ix.bits(Bind.index.depth(), Bind.key(ep), Bind.key(pp)), pp, ep, ds, at,
          e => wi.alike(ep, pp, e))) :
        {_ == Imports.deps.first(Imports.Edge{ep, ds} <> rest, pp) : List<&2, String>}
      %Equal.sym(List<&2, String>, Imports.deps.ix(Imports.edges.ix.of(rest), pp), Imports.deps.first(rest, pp),
        wi.deps(rest, pp)) :
        {Lazy.stop(List<&2, String>, String.eq(ep, pp), ds, _u => _)
          == Imports.deps.first(Imports.Edge{ep, ds} <> rest, pp) : List<&2, String>}
      {==}

# the binder's scan is the walk's
law wi.has:
  for xs: List<&2, String>
  for +dd: String
  {Bind.has_item(xs, dd) == Imports.seek(xs, dd) : Bool}

def wi.has(xs, dd):
  match xs:
    case Nil{}:
      {==}
    case Con{+hh, +rest}:
      %Equal.sym(Bool, Bind.same(hh, dd), String.eq(hh, dd), M4.ic.alike(hh, dd)) :
        {Lazy.or_else(_, _u => Bind.has_item(rest, dd)) == Imports.seek(hh <> rest, dd) : Bool}
      %Equal.sym(Bool, Bind.has_item(rest, dd), Imports.seek(rest, dd), wi.has(rest, dd)) :
        {Lazy.or_else(String.eq(hh, dd), _u => _) == Imports.seek(hh <> rest, dd) : Bool}
      {==}

# a path is in the index of some paths exactly when the walk's scan finds it
law wi.seek:
  for +xs: List<&2, String>
  for +dd: String
  {Bind.indexed(Bind.index(xs), dd) == Imports.seek(xs, dd) : Bool}

def wi.seek(xs, dd):
  Equal.trans(Bool, Bind.indexed(Bind.index(xs), dd), Bind.has_item(xs, dd), Imports.seek(xs, dd),
    L1.index_finds(xs, dd), wi.has(xs, dd))

# paths put onto the index of others are the index of them all
law wi.onto:
  for xs: List<&2, String>
  for +ys: List<&2, String>
  {Imports.seen.onto(xs, Bind.index(ys)) == Bind.index(List.append(&2, String, xs, ys)) : Bind.Index}

def wi.onto(xs, ys):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      %Equal.sym(Bind.Index, Imports.seen.onto(rest, Bind.index(ys)), Bind.index(List.append(&2, String, rest, ys)),
        wi.onto(rest, ys)) :
        {Bind.index.put(Bind.index.depth(), Bind.key(x), _, x)
          == Bind.index(List.append(&2, String, x <> rest, ys)) : Bind.Index}
      {==}

# the files found off the indexes are fresh.fast's
law wi.fresh:
  for ds: List<&2, String>
  for +seen: List<&2, String>
  for +read: List<&2, String>
  {Imports.fresh.ix(ds, Bind.index(seen), Bind.index(read)) == Imports.fresh.fast(ds, seen, read) : List<&2, String>}

def wi.fresh(ds, seen, read):
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +rest}:
      +more = Imports.fresh.fast(rest, seen, read)
      %Equal.sym(List<&2, String>, Imports.fresh.ix(rest, Bind.index(seen), Bind.index(read)), more,
        wi.fresh(rest, seen, read)) :
        {Bool.pick(List<&2, String>, Lazy.and_then(Bool.not(Imports.seek(_, d)),
          _u => Lazy.and_then(Bool.not(Bind.indexed(Bind.index(seen), d)), _v => Bind.indexed(Bind.index(read), d))),
          d <> _, _) == Imports.fresh.fast(d <> rest, seen, read) : List<&2, String>}
      %Equal.sym(Bool, Bind.indexed(Bind.index(seen), d), Imports.seek(seen, d), wi.seek(seen, d)) :
        {Bool.pick(List<&2, String>, Lazy.and_then(Bool.not(Imports.seek(more, d)),
          _u => Lazy.and_then(Bool.not(_), _v => Bind.indexed(Bind.index(read), d))),
          d <> more, more) == Imports.fresh.fast(d <> rest, seen, read) : List<&2, String>}
      %Equal.sym(Bool, Bind.indexed(Bind.index(read), d), Imports.seek(read, d), wi.seek(read, d)) :
        {Bool.pick(List<&2, String>, Lazy.and_then(Bool.not(Imports.seek(more, d)),
          _u => Lazy.and_then(Bool.not(Imports.seek(seen, d)), _v => _)),
          d <> more, more) == Imports.fresh.fast(d <> rest, seen, read) : List<&2, String>}
      {==}
