# the fast closure walk, lookups and early stops equal the spec walk
import Base
import ../../src/lazy/lazy.bend as Lazy
import ../../src/rules/imports.bend as Imports
import ../../src/rules/digest.bend as Digest
import ../../laws/ImportReachIsClosed.bend as L1
import ../../laws/defs/Unsafe.bend as D1
import ./RoleProofPicked.bend as M1
import ./UnsafeStringCompare.bend as M2
import ./UnusedEarlyOr.bend as M3

# or with False on the right is the left
law unsafe.or_false:
  for a: Bool
  {Bool.or(a, False{}) == a : Bool}

def unsafe.or_false(a):
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

# or groups either way
law unsafe.or_assoc:
  for a: Bool
  for b: Bool
  for c: Bool
  {Bool.or(Bool.or(a, b), c) == Bool.or(a, Bool.or(b, c)) : Bool}

def unsafe.or_assoc(a, _b, _c):
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

# or's first two arguments trade places
law unsafe.or_swap:
  for a: Bool
  for b: Bool
  for c: Bool
  {Bool.or(a, Bool.or(b, c)) == Bool.or(b, Bool.or(a, c)) : Bool}

def unsafe.or_swap(a, b, _c):
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

# or is True when its left is
law unsafe.or_l:
  for a: Bool
  for -b: Bool
  for e: {a == True{} : Bool}
  {Bool.or(a, b) == True{} : Bool}

def unsafe.or_l(a, b, e):
  %Equal.sym(Bool, a, True{}, e) : {Bool.or(_, b) == True{} : Bool}
  {==}

# or is True when its right is
law unsafe.or_r:
  for a: Bool
  for -b: Bool
  for e: {b == True{} : Bool}
  {Bool.or(a, b) == True{} : Bool}

def unsafe.or_r(a, _b, e):
  match a:
    case False{}:
      e
    case True{}:
      {==}

# a True and holds its left
law unsafe.and_l:
  for a: Bool
  for -b: Bool
  for e: {Bool.and(a, b) == True{} : Bool}
  {a == True{} : Bool}

def unsafe.and_l(a, _b, e):
  match a:
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, M1.unsafe.false_true(e))
    case True{}:
      {==}

# a True and holds its right
law unsafe.and_r:
  for a: Bool
  for -b: Bool
  for e: {Bool.and(a, b) == True{} : Bool}
  {b == True{} : Bool}

def unsafe.and_r(a, b, e):
  match a:
    case False{}:
      Empty.absurd({b == True{} : Bool}, M1.unsafe.false_true(e))
    case True{}:
      e

# and of two Trues is True
law unsafe.and_true:
  for a: Bool
  for -b: Bool
  for ea: {a == True{} : Bool}
  for eb: {b == True{} : Bool}
  {Bool.and(a, b) == True{} : Bool}

def unsafe.and_true(a, b, ea, eb):
  %Equal.sym(Bool, a, True{}, ea) : {Bool.and(_, b) == True{} : Bool}
  eb

# membership, as Imports.has reads it

# List.contains steps with List.any.if (bend 2.0.37): on a constructor head
# test it is Bool.or
law unsafe.any_or:
  for b: Bool
  for -r: Bool
  {List.any.if(_u => r, b) == Bool.or(b, r) : Bool}

def unsafe.any_or(b, _r):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# has on a cons is the head's test or the rest's
law unsafe.has_con:
  for +h: String
  for +t: List<&2, String>
  for +x: String
  {Imports.has(h <> t, x) == Bool.or(String.eq(h, x), Imports.has(t, x)) : Bool}

def unsafe.has_con(h, t, x):
  unsafe.any_or(String.eq(h, x), Imports.has(t, x))

# has over an append is has over either part
law unsafe.has_app:
  for xs: List<&2, String>
  for +ys: List<&2, String>
  for +x: String
  {Imports.has(List.append(&2, String, xs, ys), x) == Bool.or(Imports.has(xs, x), Imports.has(ys, x)) : Bool}

def unsafe.has_app(xs, ys, x):
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %Equal.sym(Bool, Imports.has(h <> List.append(&2, String, t, ys), x),
          Bool.or(String.eq(h, x), Imports.has(List.append(&2, String, t, ys), x)),
          unsafe.has_con(h, List.append(&2, String, t, ys), x)) :
        {_ == Bool.or(Imports.has(h <> t, x), Imports.has(ys, x)) : Bool}
      %Equal.sym(Bool, Imports.has(h <> t, x), Bool.or(String.eq(h, x), Imports.has(t, x)), unsafe.has_con(h, t, x)) :
        {Bool.or(String.eq(h, x), Imports.has(List.append(&2, String, t, ys), x))
          == Bool.or(_, Imports.has(ys, x)) : Bool}
      %Equal.sym(Bool, Imports.has(List.append(&2, String, t, ys), x), Bool.or(Imports.has(t, x), Imports.has(ys, x)),
          unsafe.has_app(t, ys, x)) :
        {Bool.or(String.eq(h, x), _) == Bool.or(Bool.or(String.eq(h, x), Imports.has(t, x)), Imports.has(ys, x)) : Bool}
      Equal.sym(Bool, Bool.or(Bool.or(String.eq(h, x), Imports.has(t, x)), Imports.has(ys, x)),
        Bool.or(String.eq(h, x), Bool.or(Imports.has(t, x), Imports.has(ys, x))),
        unsafe.or_assoc(String.eq(h, x), Imports.has(t, x), Imports.has(ys, x)))

# has over a reversal onto acc is has over either
law unsafe.has_rgo:
  for xs: List<&2, String>
  for +acc: List<&2, String>
  for +x: String
  {Imports.has(List.reverse.go(&2, String, xs, acc), x) == Bool.or(Imports.has(xs, x), Imports.has(acc, x)) : Bool}

def unsafe.has_rgo(xs, acc, x):
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %Equal.sym(Bool, Imports.has(h <> t, x), Bool.or(String.eq(h, x), Imports.has(t, x)), unsafe.has_con(h, t, x)) :
        {Imports.has(List.reverse.go(&2, String, t, h <> acc), x) == Bool.or(_, Imports.has(acc, x)) : Bool}
      ih = Equal.trans(Bool, Imports.has(List.reverse.go(&2, String, t, h <> acc), x),
        Bool.or(Imports.has(t, x), Imports.has(h <> acc, x)),
        Bool.or(Imports.has(t, x), Bool.or(String.eq(h, x), Imports.has(acc, x))),
        unsafe.has_rgo(t, h <> acc, x),
        Equal.cong(Bool, Bool, r => Bool.or(Imports.has(t, x), r), Imports.has(h <> acc, x),
          Bool.or(String.eq(h, x), Imports.has(acc, x)), unsafe.has_con(h, acc, x)))
      %Equal.sym(Bool, Imports.has(List.reverse.go(&2, String, t, h <> acc), x),
          Bool.or(Imports.has(t, x), Bool.or(String.eq(h, x), Imports.has(acc, x))),
          ih) :
        {_ == Bool.or(Bool.or(String.eq(h, x), Imports.has(t, x)), Imports.has(acc, x)) : Bool}
      %Equal.sym(Bool, Bool.or(Bool.or(String.eq(h, x), Imports.has(t, x)), Imports.has(acc, x)),
          Bool.or(String.eq(h, x), Bool.or(Imports.has(t, x), Imports.has(acc, x))),
          unsafe.or_assoc(String.eq(h, x), Imports.has(t, x), Imports.has(acc, x))) :
        {Bool.or(Imports.has(t, x), Bool.or(String.eq(h, x), Imports.has(acc, x))) == _ : Bool}
      unsafe.or_swap(Imports.has(t, x), String.eq(h, x), Imports.has(acc, x))

# has over a reversal is has
law unsafe.has_rev:
  for +xs: List<&2, String>
  for +x: String
  {Imports.has(List.reverse(&2, String, xs), x) == Imports.has(xs, x) : Bool}

def unsafe.has_rev(xs, x):
  Equal.trans(Bool, Imports.has(List.reverse(&2, String, xs), x), Bool.or(Imports.has(xs, x), False{}),
    Imports.has(xs, x), unsafe.has_rgo(xs, [], x), unsafe.or_false(Imports.has(xs, x)))

# every path of xs is held by ss
def unsafe.all_in(+ss: List<&2, String>, xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, rest}:
      +more = unsafe.all_in(ss, rest)
      Bool.and(Imports.has(ss, x), more)

# the path h, String.eq to x or not, carried to has: when it is, ss has x
# because it has h
law unsafe.has_sub.at:
  for +ss: List<&2, String>
  for +h: String
  for -t: List<&2, String>
  for +x: String
  for b: Bool
  for eb: {String.eq(h, x) == b : Bool}
  for hh: {Imports.has(ss, h) == True{} : Bool}
  for hx: {List.any.if(_u => Imports.has(t, x), b) == True{} : Bool}
  for ih: {Imports.has(t, x) == True{} : Bool} -> {Imports.has(ss, x) == True{} : Bool}
  {Imports.has(ss, x) == True{} : Bool}

def unsafe.has_sub.at(ss, h, _t, x, b, eb, hh, hx, ih):
  match b:
    case True{}:
      %M1.unsafe.seq(h, x, eb) : {Imports.has(ss, _) == True{} : Bool}
      hh
    case False{}:
      ih(hx)

# a path xs has is one ss has, when ss holds every path of xs
law unsafe.has_sub:
  for +ss: List<&2, String>
  for xs: List<&2, String>
  for +x: String
  for +ha: {unsafe.all_in(ss, xs) == True{} : Bool}
  for hx: {Imports.has(xs, x) == True{} : Bool}
  {Imports.has(ss, x) == True{} : Bool}

def unsafe.has_sub(ss, xs, x, ha, hx):
  match xs:
    case Nil{}:
      Empty.absurd({Imports.has(ss, x) == True{} : Bool}, M1.unsafe.false_true(hx))
    case Con{+h, +t}:
      unsafe.has_sub.at(ss, h, t, x, String.eq(h, x), {==}, unsafe.and_l(Imports.has(ss, h), unsafe.all_in(ss, t), ha),
        hx, z => unsafe.has_sub(ss, t, x, unsafe.and_r(Imports.has(ss, h), unsafe.all_in(ss, t), ha), z))

# a list that holds xs, with more in front, still holds it
law unsafe.in_pre:
  for +aa: List<&2, String>
  for +ss: List<&2, String>
  for xs: List<&2, String>
  for +h: {unsafe.all_in(ss, xs) == True{} : Bool}
  {unsafe.all_in(List.append(&2, String, aa, ss), xs) == True{} : Bool}

def unsafe.in_pre(aa, ss, xs, h):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      unsafe.and_true(Imports.has(List.append(&2, String, aa, ss), x),
        unsafe.all_in(List.append(&2, String, aa, ss), t),
        Equal.trans(Bool, Imports.has(List.append(&2, String, aa, ss), x),
          Bool.or(Imports.has(aa, x), Imports.has(ss, x)), True{}, unsafe.has_app(aa, ss, x),
          unsafe.or_r(Imports.has(aa, x), Imports.has(ss, x), unsafe.and_l(Imports.has(ss, x), unsafe.all_in(ss, t),
            h))),
        unsafe.in_pre(aa, ss, t, unsafe.and_r(Imports.has(ss, x), unsafe.all_in(ss, t), h)))

# a list that holds xs, with more behind, still holds it
law unsafe.in_suf:
  for +ss: List<&2, String>
  for +bb: List<&2, String>
  for xs: List<&2, String>
  for +h: {unsafe.all_in(ss, xs) == True{} : Bool}
  {unsafe.all_in(List.append(&2, String, ss, bb), xs) == True{} : Bool}

def unsafe.in_suf(ss, bb, xs, h):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      unsafe.and_true(Imports.has(List.append(&2, String, ss, bb), x),
        unsafe.all_in(List.append(&2, String, ss, bb), t),
        Equal.trans(Bool, Imports.has(List.append(&2, String, ss, bb), x),
          Bool.or(Imports.has(ss, x), Imports.has(bb, x)), True{}, unsafe.has_app(ss, bb, x),
          unsafe.or_l(Imports.has(ss, x), Imports.has(bb, x), unsafe.and_l(Imports.has(ss, x), unsafe.all_in(ss, t),
            h))),
        unsafe.in_suf(ss, bb, t, unsafe.and_r(Imports.has(ss, x), unsafe.all_in(ss, t), h)))

# a list holds itself
law unsafe.in_refl:
  for xs: List<&2, String>
  {unsafe.all_in(xs, xs) == True{} : Bool}

def unsafe.in_refl(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      unsafe.and_true(Imports.has(h <> t, h), unsafe.all_in(h <> t, t),
        Equal.trans(Bool, Imports.has(h <> t, h), Bool.or(String.eq(h, h), Imports.has(t, h)), True{},
          unsafe.has_con(h, t, h), unsafe.or_l(String.eq(h, h), Imports.has(t, h), M2.unsafe.srefl(h))),
        unsafe.in_pre([h], t, t, unsafe.in_refl(t)))

# a list that holds two lists holds them appended
law unsafe.in_app:
  for +ss: List<&2, String>
  for aa: List<&2, String>
  for +bb: List<&2, String>
  for +ha: {unsafe.all_in(ss, aa) == True{} : Bool}
  for hb: {unsafe.all_in(ss, bb) == True{} : Bool}
  {unsafe.all_in(ss, List.append(&2, String, aa, bb)) == True{} : Bool}

def unsafe.in_app(ss, aa, bb, ha, hb):
  match aa:
    case Nil{}:
      hb
    case Con{+x, +t}:
      unsafe.and_true(Imports.has(ss, x), unsafe.all_in(ss, List.append(&2, String, t, bb)),
        unsafe.and_l(Imports.has(ss, x), unsafe.all_in(ss, t), ha),
        unsafe.in_app(ss, t, bb, unsafe.and_r(Imports.has(ss, x), unsafe.all_in(ss, t), ha), hb))

# a list that holds xs and acc holds xs reversed onto acc
law unsafe.in_rgo:
  for +ss: List<&2, String>
  for xs: List<&2, String>
  for +acc: List<&2, String>
  for +hx: {unsafe.all_in(ss, xs) == True{} : Bool}
  for hacc: {unsafe.all_in(ss, acc) == True{} : Bool}
  {unsafe.all_in(ss, List.reverse.go(&2, String, xs, acc)) == True{} : Bool}

def unsafe.in_rgo(ss, xs, acc, hx, hacc):
  match xs:
    case Nil{}:
      hacc
    case Con{+x, +t}:
      unsafe.in_rgo(ss, t, x <> acc, unsafe.and_r(Imports.has(ss, x), unsafe.all_in(ss, t), hx),
        unsafe.and_true(Imports.has(ss, x), unsafe.all_in(ss, acc), unsafe.and_l(Imports.has(ss, x),
          unsafe.all_in(ss, t),
          hx), hacc))

# a list that holds xs holds it reversed
law unsafe.in_rev:
  for +ss: List<&2, String>
  for xs: List<&2, String>
  for h: {unsafe.all_in(ss, xs) == True{} : Bool}
  {unsafe.all_in(ss, List.reverse(&2, String, xs)) == True{} : Bool}

def unsafe.in_rev(ss, xs, h):
  unsafe.in_rgo(ss, xs, [], h, {==})

# a list reversed holds what it holds
law unsafe.in_rev_set:
  for +ss: List<&2, String>
  for xs: List<&2, String>
  {unsafe.all_in(List.reverse(&2, String, ss), xs) == unsafe.all_in(ss, xs) : Bool}

def unsafe.in_rev_set(ss, xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.sym(Bool, Imports.has(List.reverse(&2, String, ss), x), Imports.has(ss, x), unsafe.has_rev(ss, x)) :
        {Bool.and(_, unsafe.all_in(List.reverse(&2, String, ss), t)) == Bool.and(Imports.has(ss, x),
          unsafe.all_in(ss, t))
          : Bool}
      %Equal.sym(Bool, unsafe.all_in(List.reverse(&2, String, ss), t), unsafe.all_in(ss, t), unsafe.in_rev_set(ss, t)) :
        {Bool.and(Imports.has(ss, x), _) == Bool.and(Imports.has(ss, x), unsafe.all_in(ss, t)) : Bool}
      {==}

# the digests as the walk reads them

# the walk's graph lookup is unsafe.imports
law unsafe.deps_imports:
  for ds: List<&2, Digest.Digest>
  for +pp: String
  {Imports.deps.spec(Digest.edges(ds), pp) == D1.unsafe.imports(ds, pp) : List<&2, String>}

def unsafe.deps_imports(ds, pp):
  match ds:
    case Nil{}:
      {==}
    case Con{Digest.Digest{path, +norm, dir, is_laws, is_law_file, exempt, tops, says, +deps, laws}, +rest}:
      %Equal.sym(List<&2, String>, Imports.deps.spec(Digest.edges(rest), pp), D1.unsafe.imports(rest, pp),
          unsafe.deps_imports(rest, pp)) :
        {Bool.pick(List<&2, String>, String.eq(norm, pp), deps, _)
          == Bool.pick(List<&2, String>, String.eq(norm, pp), deps, D1.unsafe.imports(rest, pp)) : List<&2, String>}
      {==}

# the walk's read files are unsafe.read
law unsafe.read_paths:
  for ds: List<&2, Digest.Digest>
  for +pp: String
  {Imports.has(Imports.paths(Digest.edges(ds)), pp) == D1.unsafe.read(ds, pp) : Bool}

def unsafe.read_paths(ds, pp):
  match ds:
    case Nil{}:
      {==}
    case Con{Digest.Digest{path, +norm, dir, is_laws, is_law_file, exempt, tops, says, deps, laws}, +rest}:
      %Equal.sym(Bool, Imports.has(norm <> Imports.paths(Digest.edges(rest)), pp),
          Bool.or(String.eq(norm, pp), Imports.has(Imports.paths(Digest.edges(rest)), pp)),
          unsafe.has_con(norm, Imports.paths(Digest.edges(rest)), pp)) :
        {_ == Bool.or(String.eq(norm, pp), D1.unsafe.read(rest, pp)) : Bool}
      %Equal.sym(Bool, Imports.has(Imports.paths(Digest.edges(rest)), pp), D1.unsafe.read(rest, pp),
          unsafe.read_paths(rest, pp)) :
        {Bool.or(String.eq(norm, pp), _) == Bool.or(String.eq(norm, pp), D1.unsafe.read(rest, pp)) : Bool}
      {==}

# as many read files as digests
law unsafe.len_paths:
  for ds: List<&2, Digest.Digest>
  {List.length(&2, String, Imports.paths(Digest.edges(ds))) == List.length(&2, Digest.Digest, ds) : Nat}

def unsafe.len_paths(ds):
  match ds:
    case Nil{}:
      {==}
    case Con{Digest.Digest{path, norm, dir, is_laws, is_law_file, exempt, tops, says, deps, laws}, +rest}:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, String, Imports.paths(Digest.edges(rest))),
        List.length(&2, Digest.Digest, rest), unsafe.len_paths(rest))

# an or of a not: when the not's argument is True, the right is
law unsafe.or_not:
  for r: Bool
  for -h2: Bool
  for e: {Bool.or(Bool.not(r), h2) == True{} : Bool}
  for er: {r == True{} : Bool}
  {h2 == True{} : Bool}

def unsafe.or_not(r, h2, e, er):
  match r:
    case False{}:
      Empty.absurd({h2 == True{} : Bool}, M1.unsafe.false_true(er))
    case True{}:
      e

# the head of a shut list, String.eq to p or not, carried to what p imports
law unsafe.shut_at.at:
  for +ds: List<&2, Digest.Digest>
  for +ss: List<&2, String>
  for +h: String
  for -t: List<&2, String>
  for +p: String
  for b: Bool
  for eb: {String.eq(h, p) == b : Bool}
  for hh: {D1.unsafe.held(ds, ss, D1.unsafe.imports(ds, h)) == True{} : Bool}
  for hx: {List.any.if(_u => Imports.has(t, p), b) == True{} : Bool}
  for ih: {Imports.has(t, p) == True{} : Bool}
    -> {D1.unsafe.held(ds, ss, D1.unsafe.imports(ds, p)) == True{} : Bool}
  {D1.unsafe.held(ds, ss, D1.unsafe.imports(ds, p)) == True{} : Bool}

def unsafe.shut_at.at(ds, ss, h, _t, p, b, eb, hh, hx, ih):
  match b:
    case True{}:
      %M1.unsafe.seq(h, p, eb) : {D1.unsafe.held(ds, ss, D1.unsafe.imports(ds, _)) == True{} : Bool}
      hh
    case False{}:
      ih(hx)

# ss shut over ps holds what the run imports of each path ps has
law unsafe.shut_at:
  for +ds: List<&2, Digest.Digest>
  for +ss: List<&2, String>
  for ps: List<&2, String>
  for +p: String
  for +hs: {D1.unsafe.shut(ds, ss, ps) == True{} : Bool}
  for hp: {Imports.has(ps, p) == True{} : Bool}
  {D1.unsafe.held(ds, ss, D1.unsafe.imports(ds, p)) == True{} : Bool}

def unsafe.shut_at(ds, ss, ps, p, hs, hp):
  match ps:
    case Nil{}:
      Empty.absurd({D1.unsafe.held(ds, ss, D1.unsafe.imports(ds, p)) == True{} : Bool}, M1.unsafe.false_true(hp))
    case Con{+h, +t}:
      unsafe.shut_at.at(ds, ss, h, t, p, String.eq(h, p), {==},
        unsafe.and_l(D1.unsafe.held(ds, ss, D1.unsafe.imports(ds, h)), D1.unsafe.shut(ds, ss, t), hs), hp,
        z => unsafe.shut_at(ds, ss, t, p,
          unsafe.and_r(D1.unsafe.held(ds, ss, D1.unsafe.imports(ds, h)), D1.unsafe.shut(ds, ss, t), hs), z))

# one import the walk takes up, when ss holds the run's imports: kept or
# not, ss holds what comes out
law unsafe.fresh_in.at:
  for +ds: List<&2, Digest.Digest>
  for +ss: List<&2, String>
  for +seen: List<&2, String>
  for +d: String
  for +more: List<&2, String>
  for c: Bool
  for hc: {Bool.and(Bool.and(Imports.has(Imports.paths(Digest.edges(ds)), d), Bool.not(Imports.has(seen, d))),
    Bool.not(Imports.has(more, d))) == c : Bool}
  for hd: {Bool.or(Bool.not(D1.unsafe.read(ds, d)), Imports.has(ss, d)) == True{} : Bool}
  for hm: {unsafe.all_in(ss, more) == True{} : Bool}
  {unsafe.all_in(ss, Bool.pick(List<&2, String>, c, d <> more, more)) == True{} : Bool}

def unsafe.fresh_in.at(ds, ss, seen, d, more, c, hc, hd, hm):
  match c:
    case False{}:
      hm
    case True{}:
      +hr = Imports.has(Imports.paths(Digest.edges(ds)), d)
      h1 = unsafe.and_l(Bool.and(hr, Bool.not(Imports.has(seen, d))), Bool.not(Imports.has(more, d)), hc)
      h2 = unsafe.and_l(hr, Bool.not(Imports.has(seen, d)), h1)
      h3 = Equal.trans(Bool, D1.unsafe.read(ds, d), hr, True{},
        Equal.sym(Bool, hr, D1.unsafe.read(ds, d), unsafe.read_paths(ds, d)), h2)
      unsafe.and_true(Imports.has(ss, d), unsafe.all_in(ss, more),
        unsafe.or_not(D1.unsafe.read(ds, d), Imports.has(ss, d), hd, h3), hm)

# what the walk takes up from xs is held by ss, when ss holds the run's
# imports among xs
law unsafe.fresh_in:
  for +ds: List<&2, Digest.Digest>
  for +ss: List<&2, String>
  for xs: List<&2, String>
  for +seen: List<&2, String>
  for +hx: {D1.unsafe.held(ds, ss, xs) == True{} : Bool}
  {unsafe.all_in(ss, Imports.fresh.spec(xs, seen, Imports.paths(Digest.edges(ds)))) == True{} : Bool}

def unsafe.fresh_in(ds, ss, xs, seen, hx):
  match xs:
    case Nil{}:
      {==}
    case Con{+d, +rest}:
      +more = Imports.fresh.spec(rest, seen, Imports.paths(Digest.edges(ds)))
      +hd = Bool.or(Bool.not(D1.unsafe.read(ds, d)), Imports.has(ss, d))
      unsafe.fresh_in.at(ds, ss, seen, d, more,
        Bool.and(Bool.and(Imports.has(Imports.paths(Digest.edges(ds)), d), Bool.not(Imports.has(seen, d))),
          Bool.not(Imports.has(more, d))), {==},
        unsafe.and_l(hd, D1.unsafe.held(ds, ss, rest), hx),
        unsafe.fresh_in(ds, ss, rest, seen, unsafe.and_r(hd, D1.unsafe.held(ds, ss, rest), hx)))

# a shut list that holds the walk's worklist and what it has seen holds
# everything the walk returns
law unsafe.least_walk:
  for +ds: List<&2, Digest.Digest>
  for fuel: Nat
  for todo: List<&2, String>
  for +seen: List<&2, String>
  for +ss: List<&2, String>
  for +hs: {D1.unsafe.shut(ds, ss, ss) == True{} : Bool}
  for +ht: {unsafe.all_in(ss, todo) == True{} : Bool}
  for hn: {unsafe.all_in(ss, seen) == True{} : Bool}
  {unsafe.all_in(ss, Imports.walk.spec(fuel, todo, seen, Digest.edges(ds), Imports.paths(Digest.edges(ds)))) == True{}
    : Bool}

def unsafe.least_walk(ds, fuel, todo, seen, ss, hs, ht, hn):
  match fuel todo:
    case 0n _t:
      hn
    case 1n+f Nil{}:
      hn
    case 1n+f Con{+p, +rest}:
      +deps = Imports.deps.spec(Digest.edges(ds), p)
      +found = Imports.fresh.spec(deps, seen, Imports.paths(Digest.edges(ds)))
      hi = unsafe.shut_at(ds, ss, ss, p, hs, unsafe.and_l(Imports.has(ss, p), unsafe.all_in(ss, rest), ht))
      hd = Equal.trans(Bool, D1.unsafe.held(ds, ss, deps), D1.unsafe.held(ds, ss, D1.unsafe.imports(ds, p)),
        True{}, Equal.cong(List<&2, String>, Bool, z => D1.unsafe.held(ds, ss, z), deps, D1.unsafe.imports(ds, p),
          unsafe.deps_imports(ds, p)), hi)
      +hf = unsafe.fresh_in(ds, ss, deps, seen, hd)
      unsafe.least_walk(ds, f, List.append(&2, String, found, rest),
        List.append(&2, String, List.reverse(&2, String, found), seen), ss, hs,
        unsafe.in_app(ss, found, rest, hf, unsafe.and_r(Imports.has(ss, p), unsafe.all_in(ss, rest), ht)),
        unsafe.in_app(ss, List.reverse(&2, String, found), seen, unsafe.in_rev(ss, found, hf), hn))

# the walk keeps every path it has seen
law unsafe.keep:
  for +ds: List<&2, Digest.Digest>
  for fuel: Nat
  for todo: List<&2, String>
  for +seen: List<&2, String>
  for +x: String
  for hx: {Imports.has(seen, x) == True{} : Bool}
  {Imports.has(Imports.walk.spec(fuel, todo, seen, Digest.edges(ds), Imports.paths(Digest.edges(ds))),
    x) == True{} : Bool}

def unsafe.keep(ds, fuel, todo, seen, x, hx):
  match fuel todo:
    case 0n _t:
      hx
    case 1n+f Nil{}:
      hx
    case 1n+f Con{+p, +rest}:
      +found = Imports.fresh.spec(Imports.deps.spec(Digest.edges(ds), p), seen, Imports.paths(Digest.edges(ds)))
      +rf = List.reverse(&2, String, found)
      unsafe.keep(ds, f, List.append(&2, String, found, rest), List.append(&2, String, rf, seen), x,
        Equal.trans(Bool, Imports.has(List.append(&2, String, rf, seen), x),
          Bool.or(Imports.has(rf, x), Imports.has(seen, x)), True{}, unsafe.has_app(rf, seen, x),
          unsafe.or_r(Imports.has(rf, x), Imports.has(seen, x), hx)))

# the walk's lookups, stopping at the first hit, are the walk's own
# --------------------------------------------------------------------

# `seek` is `has`
law imp.seek:
  for ps: List<&2, String>
  for +pp: String
  {Imports.seek(ps, pp) == Imports.has(ps, pp) : Bool}

def imp.seek(ps, pp):
  match ps:
    case Nil{}:
      {==}
    case Con{+p, +rest}:
      Equal.trans(Bool, Lazy.or_else(String.eq(p, pp), _u => Imports.seek(rest, pp)),
        Bool.or(String.eq(p, pp), Imports.has(rest, pp)), Imports.has(p <> rest, pp),
        M3.unused.or(String.eq(p, pp), Imports.seek(rest, pp), Imports.has(rest, pp), imp.seek(rest, pp)),
        Equal.sym(Bool, Imports.has(p <> rest, pp), Bool.or(String.eq(p, pp), Imports.has(rest, pp)),
          unsafe.has_con(p, rest, pp)))

# an early exit on the first hit is the pick that computed the rest anyway
law imp.stop:
  for c: Bool
  for -a: List<&2, String>
  for -x: List<&2, String>
  for -y: List<&2, String>
  for ih: {x == y : List<&2, String>}
  {Lazy.stop(List<&2, String>, c, a, _u => x) == Bool.pick(List<&2, String>, c, a, y) : List<&2, String>}

def imp.stop(c, _a, _x, _y, ih):
  match c:
    case True{}:
      {==}
    case False{}:
      ih

# `deps.first` is `deps.spec`
law imp.deps:
  for es: List<&2, Imports.Edge>
  for +pp: String
  {Imports.deps.first(es, pp) == Imports.deps.spec(es, pp) : List<&2, String>}

def imp.deps(es, pp):
  match es:
    case Nil{}:
      {==}
    case Con{Imports.Edge{+ep, +ds}, +rest}:
      imp.stop(String.eq(ep, pp), ds, Imports.deps.first(rest, pp), Imports.deps.spec(rest, pp), imp.deps(rest, pp))

# the three tests of `fresh`, asked short-circuit and in the other order
law imp.cond:
  for m: Bool
  for s: Bool
  for r: Bool
  {Lazy.and_then(Bool.not(m), _u => Lazy.and_then(Bool.not(s), _v => r)) == Bool.and(Bool.and(r, Bool.not(s)),
    Bool.not(m)) : Bool}

def imp.cond(m, s, r):
  match m:
    case True{}:
      match s:
        case True{}:
          match r:
            case True{}:
              {==}
            case False{}:
              {==}
        case False{}:
          match r:
            case True{}:
              {==}
            case False{}:
              {==}
    case False{}:
      match s:
        case True{}:
          match r:
            case True{}:
              {==}
            case False{}:
              {==}
        case False{}:
          match r:
            case True{}:
              {==}
            case False{}:
              {==}

# `fresh.fast` is `fresh`
law imp.fresh:
  for ds: List<&2, String>
  for +seen: List<&2, String>
  for +read: List<&2, String>
  {Imports.fresh.fast(ds, seen, read) == Imports.fresh.spec(ds, seen, read) : List<&2, String>}

def imp.fresh(ds, seen, read):
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +rest}:
      +more = Imports.fresh.spec(rest, seen, read)
      +c = Bool.and(Bool.and(Imports.has(read, d), Bool.not(Imports.has(seen, d))), Bool.not(Imports.has(more, d)))
      %Equal.sym(List<&2, String>, Imports.fresh.fast(rest, seen, read), more, imp.fresh(rest, seen, read)) :
        {Bool.pick(List<&2, String>, Lazy.and_then(Bool.not(Imports.seek(_, d)),
          _u => Lazy.and_then(Bool.not(Imports.seek(seen, d)), _v => Imports.seek(read, d))), d <> _, _)
          == Bool.pick(List<&2, String>, c, d <> more, more) : List<&2, String>}
      %Equal.sym(Bool, Imports.seek(more, d), Imports.has(more, d), imp.seek(more, d)) :
        {Bool.pick(List<&2, String>, Lazy.and_then(Bool.not(_),
          _u => Lazy.and_then(Bool.not(Imports.seek(seen, d)), _v => Imports.seek(read, d))), d <> more, more)
          == Bool.pick(List<&2, String>, c, d <> more, more) : List<&2, String>}
      %Equal.sym(Bool, Imports.seek(seen, d), Imports.has(seen, d), imp.seek(seen, d)) :
        {Bool.pick(List<&2, String>, Lazy.and_then(Bool.not(Imports.has(more, d)),
          _u => Lazy.and_then(Bool.not(_), _v => Imports.seek(read, d))), d <> more, more)
          == Bool.pick(List<&2, String>, c, d <> more, more) : List<&2, String>}
      %Equal.sym(Bool, Imports.seek(read, d), Imports.has(read, d), imp.seek(read, d)) :
        {Bool.pick(List<&2, String>, Lazy.and_then(Bool.not(Imports.has(more, d)),
          _u => Lazy.and_then(Bool.not(Imports.has(seen, d)), _v => _)), d <> more, more)
          == Bool.pick(List<&2, String>, c, d <> more, more) : List<&2, String>}
      %Equal.sym(Bool, Lazy.and_then(Bool.not(Imports.has(more, d)),
          _u => Lazy.and_then(Bool.not(Imports.has(seen, d)), _v => Imports.has(read, d))), c,
          imp.cond(Imports.has(more, d), Imports.has(seen, d), Imports.has(read, d))) :
        {Bool.pick(List<&2, String>, _, d <> more, more) == Bool.pick(List<&2, String>, c, d <> more, more)
          : List<&2, String>}
      {==}

# the walk through the fast lookups is the walk
law imp.walk:
  for fuel: Nat
  for todo: List<&2, String>
  for +seen: List<&2, String>
  for +es: List<&2, Imports.Edge>
  for +read: List<&2, String>
  {Imports.walk(fuel, todo, seen, es, read) == Imports.walk.spec(fuel, todo, seen, es, read) : List<&2, String>}

def imp.walk(fuel, todo, seen, es, read):
  match fuel todo:
    case 0n _t:
      {==}
    case 1n+f Nil{}:
      {==}
    case 1n+f Con{+p, +rest}:
      +found = Imports.fresh.spec(Imports.deps.spec(es, p), seen, read)
      +ef = Equal.trans(List<&2, String>, Imports.fresh.fast(Imports.deps.first(es, p), seen, read),
        Imports.fresh.spec(Imports.deps.first(es, p), seen, read), found,
        imp.fresh(Imports.deps.first(es, p), seen, read),
        Equal.cong(List<&2, String>, List<&2, String>, z => Imports.fresh.spec(z, seen, read),
          Imports.deps.first(es, p), Imports.deps.spec(es, p), imp.deps(es, p)))
      %Equal.sym(List<&2, String>, Imports.fresh.fast(Imports.deps.first(es, p), seen, read), found, ef) :
        {Imports.walk(f, List.append(&2, String, _, rest), List.append(&2, String, List.reverse(&2, String, _), seen),
          es, read) == Imports.walk.spec(f, List.append(&2, String, found, rest),
          List.append(&2, String, List.reverse(&2, String, found), seen), es, read) : List<&2, String>}
      imp.walk(f, List.append(&2, String, found, rest), List.append(&2, String, List.reverse(&2, String, found), seen),
        es, read)

# the closure, walked fast, is the walk's
law imp.closure:
  for +ds: List<&2, Digest.Digest>
  for +from: String
  {Imports.walk(List.length(&2, Digest.Digest, ds), [from], [from], Digest.edges(ds), Imports.paths(Digest.edges(ds)))
    == Imports.walk.spec(List.length(&2, Digest.Digest, ds), [from], [from], Digest.edges(ds),
      Imports.paths(Digest.edges(ds))) : List<&2, String>}

def imp.closure(ds, from):
  imp.walk(List.length(&2, Digest.Digest, ds), [from], [from], Digest.edges(ds), Imports.paths(Digest.edges(ds)))

def L1.unsafe_from(ds, from):
  +ww = Imports.walk.spec(List.length(&2, Digest.Digest, ds), [from], [from], Digest.edges(ds),
    Imports.paths(Digest.edges(ds)))
  %Equal.sym(List<&2, String>, Imports.walk(List.length(&2, Digest.Digest, ds), [from], [from], Digest.edges(ds),
      Imports.paths(Digest.edges(ds))), ww, imp.closure(ds, from)) :
    {Imports.has(List.reverse(&2, String, _), from) == True{} : Bool}
  Equal.trans(Bool, Imports.has(List.reverse(&2, String, ww), from), Imports.has(ww, from), True{},
    unsafe.has_rev(ww, from),
    unsafe.keep(ds, List.length(&2, Digest.Digest, ds), [from], [from], from,
      Equal.trans(Bool, Imports.has([from], from), Bool.or(String.eq(from, from), False{}), True{},
        unsafe.has_con(from, [], from), unsafe.or_l(String.eq(from, from), False{}, M2.unsafe.srefl(from)))))

def L1.unsafe_least(ds, from, ss, pp, hf, hs, hw):
  +ww = Imports.walk.spec(List.length(&2, Digest.Digest, ds), [from], [from], Digest.edges(ds),
    Imports.paths(Digest.edges(ds)))
  +wf = Imports.walk(List.length(&2, Digest.Digest, ds), [from], [from], Digest.edges(ds),
    Imports.paths(Digest.edges(ds)))
  +hp = Equal.trans(Bool, Imports.has(List.reverse(&2, String, ww), pp), Imports.has(List.reverse(&2, String, wf), pp),
    True{}, Equal.cong(List<&2, String>, Bool, z => Imports.has(List.reverse(&2, String, z), pp), ww, wf,
      Equal.sym(List<&2, String>, wf, ww, imp.closure(ds, from))), hw)
  +h1 = unsafe.and_true(Imports.has(ss, from), True{}, hf, {==})
  unsafe.has_sub(ss, ww, pp, unsafe.least_walk(ds, List.length(&2, Digest.Digest, ds), [from], [from], ss, hs, h1, h1),
    Equal.trans(Bool, Imports.has(ww, pp), Imports.has(List.reverse(&2, String, ww), pp), True{},
      Equal.sym(Bool, Imports.has(List.reverse(&2, String, ww), pp), Imports.has(ww, pp), unsafe.has_rev(ww, pp)), hp))

# the walk's invariant over qs: each path of qs is still on the worklist, or
# what the run has of its imports is seen
def unsafe.inv(
  +ds: List<&2, Digest.Digest>,
  +todo: List<&2, String>,
  +seen: List<&2, String>,
  qs: List<&2, String>
) -> Bool:
  match qs:
    case Nil{}:
      True{}
    case Con{+q, rest}:
      +more = unsafe.inv(ds, todo, seen, rest)
      Bool.and(Bool.or(Imports.has(todo, q), D1.unsafe.held(ds, seen, D1.unsafe.imports(ds, q))), more)

# with the worklist empty, the invariant is shut
law unsafe.inv_nil:
  for +ds: List<&2, Digest.Digest>
  for +seen: List<&2, String>
  for qs: List<&2, String>
  {unsafe.inv(ds, [], seen, qs) == D1.unsafe.shut(ds, seen, qs) : Bool}

def unsafe.inv_nil(ds, seen, qs):
  match qs:
    case Nil{}:
      {==}
    case Con{+q, +t}:
      %Equal.sym(Bool, unsafe.inv(ds, [], seen, t), D1.unsafe.shut(ds, seen, t), unsafe.inv_nil(ds, seen, t)) :
        {Bool.and(D1.unsafe.held(ds, seen, D1.unsafe.imports(ds, q)), _)
          == Bool.and(D1.unsafe.held(ds, seen, D1.unsafe.imports(ds, q)), D1.unsafe.shut(ds, seen, t)) : Bool}
      {==}

# paths the worklist holds keep the invariant
law unsafe.inv_todo:
  for +ds: List<&2, Digest.Digest>
  for +todo: List<&2, String>
  for +seen: List<&2, String>
  for qs: List<&2, String>
  for +h: {unsafe.all_in(todo, qs) == True{} : Bool}
  {unsafe.inv(ds, todo, seen, qs) == True{} : Bool}

def unsafe.inv_todo(ds, todo, seen, qs, h):
  match qs:
    case Nil{}:
      {==}
    case Con{+q, +t}:
      unsafe.and_true(Bool.or(Imports.has(todo, q), D1.unsafe.held(ds, seen, D1.unsafe.imports(ds, q))),
        unsafe.inv(ds, todo, seen, t),
        unsafe.or_l(Imports.has(todo, q), D1.unsafe.held(ds, seen, D1.unsafe.imports(ds, q)),
          unsafe.and_l(Imports.has(todo, q), unsafe.all_in(todo, t), h)),
        unsafe.inv_todo(ds, todo, seen, t, unsafe.and_r(Imports.has(todo, q), unsafe.all_in(todo, t), h)))

# the invariant over two lists is the invariant over them appended
law unsafe.inv_app:
  for +ds: List<&2, Digest.Digest>
  for +todo: List<&2, String>
  for +seen: List<&2, String>
  for aa: List<&2, String>
  for +bb: List<&2, String>
  for +ha: {unsafe.inv(ds, todo, seen, aa) == True{} : Bool}
  for hb: {unsafe.inv(ds, todo, seen, bb) == True{} : Bool}
  {unsafe.inv(ds, todo, seen, List.append(&2, String, aa, bb)) == True{} : Bool}

def unsafe.inv_app(ds, todo, seen, aa, bb, ha, hb):
  match aa:
    case Nil{}:
      hb
    case Con{+q, +t}:
      +hq = Bool.or(Imports.has(todo, q), D1.unsafe.held(ds, seen, D1.unsafe.imports(ds, q)))
      unsafe.and_true(hq, unsafe.inv(ds, todo, seen, List.append(&2, String, t, bb)),
        unsafe.and_l(hq, unsafe.inv(ds, todo, seen, t), ha),
        unsafe.inv_app(ds, todo, seen, t, bb, unsafe.and_r(hq, unsafe.inv(ds, todo, seen, t), ha), hb))

# one import, held in a list or not, carried to a list that holds that list
law unsafe.held_grow.at:
  for +ds: List<&2, Digest.Digest>
  for +ss: List<&2, String>
  for +tt: List<&2, String>
  for +d: String
  for b: Bool
  for eb: {Imports.has(ss, d) == b : Bool}
  for hst: {unsafe.all_in(tt, ss) == True{} : Bool}
  for hh: {Bool.or(Bool.not(D1.unsafe.read(ds, d)), b) == True{} : Bool}
  {Bool.or(Bool.not(D1.unsafe.read(ds, d)), Imports.has(tt, d)) == True{} : Bool}

def unsafe.held_grow.at(ds, ss, tt, d, b, eb, hst, hh):
  match b:
    case True{}:
      unsafe.or_r(Bool.not(D1.unsafe.read(ds, d)), Imports.has(tt, d), unsafe.has_sub(tt, ss, d, hst, eb))
    case False{}:
      +nr = Bool.not(D1.unsafe.read(ds, d))
      unsafe.or_l(nr, Imports.has(tt, d), Equal.trans(Bool, nr, Bool.or(nr, False{}), True{},
        Equal.sym(Bool, Bool.or(nr, False{}), nr, unsafe.or_false(nr)), hh))

# what the run imports among xs, held in ss, is held in a list that holds ss
law unsafe.held_grow:
  for +ds: List<&2, Digest.Digest>
  for +ss: List<&2, String>
  for +tt: List<&2, String>
  for xs: List<&2, String>
  for +h: {D1.unsafe.held(ds, ss, xs) == True{} : Bool}
  for +hst: {unsafe.all_in(tt, ss) == True{} : Bool}
  {D1.unsafe.held(ds, tt, xs) == True{} : Bool}

def unsafe.held_grow(ds, ss, tt, xs, h, hst):
  match xs:
    case Nil{}:
      {==}
    case Con{+d, +rest}:
      +hd = Bool.or(Bool.not(D1.unsafe.read(ds, d)), Imports.has(ss, d))
      unsafe.and_true(Bool.or(Bool.not(D1.unsafe.read(ds, d)), Imports.has(tt, d)), D1.unsafe.held(ds, tt, rest),
        unsafe.held_grow.at(ds, ss, tt, d, Imports.has(ss, d), {==}, hst,
          unsafe.and_l(hd, D1.unsafe.held(ds, ss, rest), h)),
        unsafe.held_grow(ds, ss, tt, rest, unsafe.and_r(hd, D1.unsafe.held(ds, ss, rest), h), hst))

# what the walk takes up, kept or not, leaves the rest of it held
law unsafe.fresh_more:
  for +ss: List<&2, String>
  for +d: String
  for +more: List<&2, String>
  for c: Bool
  for h: {unsafe.all_in(ss, Bool.pick(List<&2, String>, c, d <> more, more)) == True{} : Bool}
  {unsafe.all_in(ss, more) == True{} : Bool}

def unsafe.fresh_more(ss, d, more, c, h):
  match c:
    case True{}:
      unsafe.and_r(Imports.has(ss, d), unsafe.all_in(ss, more), h)
    case False{}:
      h

# one import the walk looks at: in the run, it was seen, is taken up later,
# or is taken up now, so a list that holds all three holds it
law unsafe.fresh_held.at:
  for +ds: List<&2, Digest.Digest>
  for +ss: List<&2, String>
  for +seen: List<&2, String>
  for +d: String
  for +more: List<&2, String>
  for b1: Bool
  for b2: Bool
  for b3: Bool
  for e1: {Imports.has(Imports.paths(Digest.edges(ds)), d) == b1 : Bool}
  for e2: {Imports.has(seen, d) == b2 : Bool}
  for e3: {Imports.has(more, d) == b3 : Bool}
  for hs: {unsafe.all_in(ss, seen) == True{} : Bool}
  for hm: {unsafe.all_in(ss, more) == True{} : Bool}
  for hf: {unsafe.all_in(ss, Bool.pick(List<&2, String>, Bool.and(Bool.and(b1, Bool.not(b2)), Bool.not(b3)), d <> more,
    more)) == True{} : Bool}
  {Bool.or(Bool.not(D1.unsafe.read(ds, d)), Imports.has(ss, d)) == True{} : Bool}

def unsafe.fresh_held.at(ds, ss, seen, d, more, b1, b2, b3, e1, e2, e3, hs, hm, hf):
  match b1:
    case False{}:
      er = Equal.trans(Bool, D1.unsafe.read(ds, d), Imports.has(Imports.paths(Digest.edges(ds)), d), False{},
        Equal.sym(Bool, Imports.has(Imports.paths(Digest.edges(ds)), d), D1.unsafe.read(ds, d),
          unsafe.read_paths(ds, d)), e1)
      %Equal.sym(Bool, D1.unsafe.read(ds, d), False{}, er) :
        {Bool.or(Bool.not(_), Imports.has(ss, d)) == True{} : Bool}
      {==}
    case True{}:
      match b2:
        case True{}:
          unsafe.or_r(Bool.not(D1.unsafe.read(ds, d)), Imports.has(ss, d), unsafe.has_sub(ss, seen, d, hs, e2))
        case False{}:
          match b3:
            case True{}:
              unsafe.or_r(Bool.not(D1.unsafe.read(ds, d)), Imports.has(ss, d), unsafe.has_sub(ss, more, d, hm, e3))
            case False{}:
              unsafe.or_r(Bool.not(D1.unsafe.read(ds, d)), Imports.has(ss, d),
                unsafe.and_l(Imports.has(ss, d), unsafe.all_in(ss, more), hf))

# a list that holds what the walk has seen and what it takes up from xs
# holds every import of xs in the run
law unsafe.fresh_held:
  for +ds: List<&2, Digest.Digest>
  for +ss: List<&2, String>
  for xs: List<&2, String>
  for +seen: List<&2, String>
  for +hs: {unsafe.all_in(ss, seen) == True{} : Bool}
  for +hf: {unsafe.all_in(ss, Imports.fresh.spec(xs, seen, Imports.paths(Digest.edges(ds)))) == True{} : Bool}
  {D1.unsafe.held(ds, ss, xs) == True{} : Bool}

def unsafe.fresh_held(ds, ss, xs, seen, hs, hf):
  match xs:
    case Nil{}:
      {==}
    case Con{+d, +rest}:
      +more = Imports.fresh.spec(rest, seen, Imports.paths(Digest.edges(ds)))
      +b1 = Imports.has(Imports.paths(Digest.edges(ds)), d)
      +b2 = Imports.has(seen, d)
      +b3 = Imports.has(more, d)
      +hm = unsafe.fresh_more(ss, d, more, Bool.and(Bool.and(b1, Bool.not(b2)), Bool.not(b3)), hf)
      unsafe.and_true(Bool.or(Bool.not(D1.unsafe.read(ds, d)), Imports.has(ss, d)), D1.unsafe.held(ds, ss, rest),
        unsafe.fresh_held.at(ds, ss, seen, d, more, b1, b2, b3, {==}, {==}, {==}, hs, hm, hf),
        unsafe.fresh_held(ds, ss, rest, seen, hs, hm))

# one path of what was seen, before a step of the walk and after it: still
# on the worklist, or its imports in the run seen
law unsafe.inv_keep.at:
  for +ds: List<&2, Digest.Digest>
  for +p: String
  for +rest: List<&2, String>
  for +seen: List<&2, String>
  for +found: List<&2, String>
  for +seen2: List<&2, String>
  for +q: String
  for b1: Bool
  for b2: Bool
  for b3: Bool
  for e1: {D1.unsafe.held(ds, seen, D1.unsafe.imports(ds, q)) == b1 : Bool}
  for e2: {String.eq(p, q) == b2 : Bool}
  for e3: {Imports.has(rest, q) == b3 : Bool}
  for hp: {D1.unsafe.held(ds, seen2, D1.unsafe.imports(ds, p)) == True{} : Bool}
  for hg: {unsafe.all_in(seen2, seen) == True{} : Bool}
  for h0: {Bool.or(List.any.if(_u => b3, b2), b1) == True{} : Bool}
  {Bool.or(Imports.has(List.append(&2, String, found, rest), q), D1.unsafe.held(ds, seen2, D1.unsafe.imports(ds,
    q)))
    == True{} : Bool}

def unsafe.inv_keep.at(ds, p, rest, seen, found, seen2, q, b1, b2, b3, e1, e2, e3, hp, hg, h0):
  match b1:
    case True{}:
      unsafe.or_r(Imports.has(List.append(&2, String, found, rest), q),
        D1.unsafe.held(ds, seen2, D1.unsafe.imports(ds, q)),
        unsafe.held_grow(ds, seen, seen2, D1.unsafe.imports(ds, q), e1, hg))
    case False{}:
      match b2:
        case True{}:
          %M1.unsafe.seq(p, q, e2) :
            {Bool.or(Imports.has(List.append(&2, String, found, rest), q),
              D1.unsafe.held(ds, seen2, D1.unsafe.imports(ds, _))) == True{} : Bool}
          unsafe.or_r(Imports.has(List.append(&2, String, found, rest), q),
            D1.unsafe.held(ds, seen2, D1.unsafe.imports(ds, p)), hp)
        case False{}:
          match b3:
            case True{}:
              +app = List.append(&2, String, found, rest)
              unsafe.or_l(Imports.has(app, q), D1.unsafe.held(ds, seen2, D1.unsafe.imports(ds, q)),
                Equal.trans(Bool, Imports.has(app, q), Bool.or(Imports.has(found, q), Imports.has(rest, q)), True{},
                  unsafe.has_app(found, rest, q), unsafe.or_r(Imports.has(found, q), Imports.has(rest, q), e3)))
            case False{}:
              Empty.absurd({Bool.or(Imports.has(List.append(&2, String, found, rest), q),
                D1.unsafe.held(ds, seen2, D1.unsafe.imports(ds, q))) == True{} : Bool}, M1.unsafe.false_true(h0))

# what was seen keeps the invariant across a step of the walk, when the
# step's new list holds the old one and what p imports from the run
law unsafe.inv_keep:
  for +ds: List<&2, Digest.Digest>
  for +p: String
  for +rest: List<&2, String>
  for +seen: List<&2, String>
  for +found: List<&2, String>
  for +seen2: List<&2, String>
  for qs: List<&2, String>
  for +hp: {D1.unsafe.held(ds, seen2, D1.unsafe.imports(ds, p)) == True{} : Bool}
  for +hg: {unsafe.all_in(seen2, seen) == True{} : Bool}
  for +hi: {unsafe.inv(ds, p <> rest, seen, qs) == True{} : Bool}
  {unsafe.inv(ds, List.append(&2, String, found, rest), seen2, qs) == True{} : Bool}

def unsafe.inv_keep(ds, p, rest, seen, found, seen2, qs, hp, hg, hi):
  match qs:
    case Nil{}:
      {==}
    case Con{+q, +t}:
      +b1 = D1.unsafe.held(ds, seen, D1.unsafe.imports(ds, q))
      +hq = Bool.or(Imports.has(p <> rest, q), b1)
      unsafe.and_true(
        Bool.or(Imports.has(List.append(&2, String, found, rest), q), D1.unsafe.held(ds, seen2,
          D1.unsafe.imports(ds, q))),
        unsafe.inv(ds, List.append(&2, String, found, rest), seen2, t),
        unsafe.inv_keep.at(ds, p, rest, seen, found, seen2, q, b1, String.eq(p, q), Imports.has(rest, q), {==}, {==},
          {==}, hp, hg, unsafe.and_l(hq, unsafe.inv(ds, p <> rest, seen, t), hi)),
        unsafe.inv_keep(ds, p, rest, seen, found, seen2, t, hp, hg, unsafe.and_r(hq, unsafe.inv(ds, p <> rest, seen, t),
          hi)))

# the walk's fuel: a count of the read files it has not seen yet

# adding 0 on the right
law unsafe.add_zero:
  for a: Nat
  {Nat.add(a, 0n) == a : Nat}

def unsafe.add_zero(a):
  match a:
    case 0n:
      {==}
    case 1n+(+p):
      Equal.cong(Nat, Nat, n => 1n+n, Nat.add(p, 0n), p, unsafe.add_zero(p))

# adding a successor on the right
law unsafe.add_succ:
  for a: Nat
  for +b: Nat
  {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}

def unsafe.add_succ(a, b):
  match a:
    case 0n:
      {==}
    case 1n+(+p):
      Equal.cong(Nat, Nat, n => 1n+n, Nat.add(p, 1n+b), 1n+Nat.add(p, b), unsafe.add_succ(p, b))

# add groups either way
law unsafe.add_assoc:
  for a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}

def unsafe.add_assoc(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+(+p):
      Equal.cong(Nat, Nat, n => 1n+n, Nat.add(Nat.add(p, b), c), Nat.add(p, Nat.add(b, c)), unsafe.add_assoc(p, b, c))

# add's first two arguments trade places
law unsafe.add_swap:
  for a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.add(a, Nat.add(b, c)) == Nat.add(b, Nat.add(a, c)) : Nat}

def unsafe.add_swap(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+(+p):
      Equal.trans(Nat, 1n+Nat.add(p, Nat.add(b, c)), 1n+Nat.add(b, Nat.add(p, c)), Nat.add(b, 1n+Nat.add(p, c)),
        Equal.cong(Nat, Nat, n => 1n+n, Nat.add(p, Nat.add(b, c)), Nat.add(b, Nat.add(p, c)), unsafe.add_swap(p, b, c)),
        Equal.sym(Nat, Nat.add(b, 1n+Nat.add(p, c)), 1n+Nat.add(b, Nat.add(p, c)), unsafe.add_succ(b, Nat.add(p, c))))

# an append is as long as its parts together
law unsafe.len_app:
  for xs: List<&2, String>
  for +ys: List<&2, String>
  {List.length(&2, String, List.append(&2, String, xs, ys))
    == Nat.add(List.length(&2, String, xs), List.length(&2, String, ys)) : Nat}

def unsafe.len_app(xs, ys):
  match xs:
    case Nil{}:
      {==}
    case Con{h, +t}:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, String, List.append(&2, String, t, ys)),
        Nat.add(List.length(&2, String, t), List.length(&2, String, ys)), unsafe.len_app(t, ys))

# the Nat before a successor
def unsafe.pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

# successors that are equal are of equal Nats
law unsafe.succ_inj:
  for -a: Nat
  for -b: Nat
  for e: {1n+a == 1n+b : Nat}
  {a == b : Nat}

def unsafe.succ_inj(a, b, e):
  Equal.cong(Nat, Nat, n => unsafe.pred(n), 1n+a, 1n+b, e)

# Unit for 0, Empty for a successor
def unsafe.nat_ty(n: Nat) -> Type:
  match n:
    case 0n:
      Unit
    case 1n+_p:
      Empty

# 0 is no successor
law unsafe.zero_succ:
  for -a: Nat
  for e: {0n == 1n+a : Nat}
  Empty

def unsafe.zero_succ(_a, e):
  %e : unsafe.nat_ty(_)
  Unit{}

# the step's sum, regrouped: the fuel left after a step against the step's
# new worklist and its new count
law unsafe.count_arith:
  for -f: Nat
  for +l: Nat
  for -m: Nat
  for +k: Nat
  for +ff: Nat
  for -la: Nat
  for +m2: Nat
  for -m3: Nat
  for +s: Nat
  for h1: {f == Nat.add(l, Nat.add(m, k)) : Nat}
  for h2: {m == Nat.add(ff, Nat.add(m2, s)) : Nat}
  for h3: {la == Nat.add(ff, l) : Nat}
  for h4: {m3 == m2 : Nat}
  {f == Nat.add(la, Nat.add(m3, Nat.add(s, k))) : Nat}

def unsafe.count_arith(f, l, m, k, ff, la, m2, m3, s, h1, h2, h3, h4):
  %Equal.sym(Nat, f, Nat.add(l, Nat.add(m, k)), h1) : {_ == Nat.add(la, Nat.add(m3, Nat.add(s, k))) : Nat}
  %Equal.sym(Nat, m, Nat.add(ff, Nat.add(m2, s)), h2) :
    {Nat.add(l, Nat.add(_, k)) == Nat.add(la, Nat.add(m3, Nat.add(s, k))) : Nat}
  %Equal.sym(Nat, la, Nat.add(ff, l), h3) :
    {Nat.add(l, Nat.add(Nat.add(ff, Nat.add(m2, s)), k)) == Nat.add(_, Nat.add(m3, Nat.add(s, k))) : Nat}
  %Equal.sym(Nat, m3, m2, h4) :
    {Nat.add(l, Nat.add(Nat.add(ff, Nat.add(m2, s)), k)) == Nat.add(Nat.add(ff, l), Nat.add(_, Nat.add(s, k))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(ff, Nat.add(m2, s)), k), Nat.add(ff, Nat.add(Nat.add(m2, s), k)),
      unsafe.add_assoc(ff, Nat.add(m2, s), k)) :
    {Nat.add(l, _) == Nat.add(Nat.add(ff, l), Nat.add(m2, Nat.add(s, k))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(m2, s), k), Nat.add(m2, Nat.add(s, k)), unsafe.add_assoc(m2, s, k)) :
    {Nat.add(l, Nat.add(ff, _)) == Nat.add(Nat.add(ff, l), Nat.add(m2, Nat.add(s, k))) : Nat}
  +yy = Nat.add(m2, Nat.add(s, k))
  Equal.trans(Nat, Nat.add(l, Nat.add(ff, yy)), Nat.add(ff, Nat.add(l, yy)), Nat.add(Nat.add(ff, l), yy),
    unsafe.add_swap(l, ff, yy), Equal.sym(Nat, Nat.add(Nat.add(ff, l), yy), Nat.add(ff, Nat.add(l, yy)),
      unsafe.add_assoc(ff, l, yy)))

# how many paths of rr ss does not have
def unsafe.miss(rr: List<&2, String>, +ss: List<&2, String>) -> Nat:
  match rr:
    case Nil{}:
      0n
    case Con{+h, t}:
      +more = unsafe.miss(t, ss)
      Bool.pick(Nat, Imports.has(ss, h), more, 1n+more)

# an empty list misses every path
law unsafe.miss_nil:
  for rr: List<&2, String>
  {unsafe.miss(rr, []) == List.length(&2, String, rr) : Nat}

def unsafe.miss_nil(rr):
  match rr:
    case Nil{}:
      {==}
    case Con{h, +t}:
      Equal.cong(Nat, Nat, n => 1n+n, unsafe.miss(t, []), List.length(&2, String, t), unsafe.miss_nil(t))

# the count does not see a reversal in front
law unsafe.miss_rev:
  for rr: List<&2, String>
  for +xs: List<&2, String>
  for +ss: List<&2, String>
  {unsafe.miss(rr, List.append(&2, String, List.reverse(&2, String, xs), ss))
    == unsafe.miss(rr, List.append(&2, String, xs, ss)) : Nat}

def unsafe.miss_rev(rr, xs, ss):
  match rr:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      +rv = List.reverse(&2, String, xs)
      +aa = List.append(&2, String, rv, ss)
      +bb = List.append(&2, String, xs, ss)
      eh = Equal.trans(Bool, Imports.has(aa, h), Bool.or(Imports.has(rv, h), Imports.has(ss, h)), Imports.has(bb, h),
        unsafe.has_app(rv, ss, h),
        Equal.trans(Bool, Bool.or(Imports.has(rv, h), Imports.has(ss, h)), Bool.or(Imports.has(xs, h),
          Imports.has(ss, h)),
          Imports.has(bb, h),
          Equal.cong(Bool, Bool, z => Bool.or(z, Imports.has(ss, h)), Imports.has(rv, h), Imports.has(xs, h),
            unsafe.has_rev(xs, h)),
          Equal.sym(Bool, Imports.has(bb, h), Bool.or(Imports.has(xs, h), Imports.has(ss, h)), unsafe.has_app(xs, ss,
            h))))
      %Equal.sym(Bool, Imports.has(aa, h), Imports.has(bb, h), eh) :
        {Bool.pick(Nat, _, unsafe.miss(t, aa), 1n+unsafe.miss(t, aa))
          == Bool.pick(Nat, Imports.has(bb, h), unsafe.miss(t, bb), 1n+unsafe.miss(t, bb)) : Nat}
      %Equal.sym(Nat, unsafe.miss(t, aa), unsafe.miss(t, bb), unsafe.miss_rev(t, xs, ss)) :
        {Bool.pick(Nat, Imports.has(bb, h), _, 1n+_)
          == Bool.pick(Nat, Imports.has(bb, h), unsafe.miss(t, bb), 1n+unsafe.miss(t, bb)) : Nat}
      {==}

# a count and a slack, both one more
law unsafe.lift1:
  for -a: Nat
  for -b: Nat
  for w: &s: Nat -> {a == Nat.add(b, s) : Nat}
  exs s2: Nat
  {1n+a == 1n+Nat.add(b, s2) : Nat}

def unsafe.lift1(a, b, w):
  (s, e) = w
  (s, Equal.cong(Nat, Nat, n => 1n+n, a, Nat.add(b, s), e))

# a count one more, with the slack one more
law unsafe.lift2:
  for -a: Nat
  for +b: Nat
  for w: &s: Nat -> {a == Nat.add(b, s) : Nat}
  exs s2: Nat
  {1n+a == Nat.add(b, s2) : Nat}

def unsafe.lift2(a, b, w):
  (s, e) = w
  +s1 = {s : Nat}
  (1n+s1, Equal.trans(Nat, 1n+a, 1n+Nat.add(b, s1), Nat.add(b, 1n+s1),
    Equal.cong(Nat, Nat, n => 1n+n, a, Nat.add(b, s1), e),
    Equal.sym(Nat, Nat.add(b, 1n+s1), 1n+Nat.add(b, s1), unsafe.add_succ(b, s1))))

# one path of rr against d on top of tt: the count without d is no smaller
law unsafe.miss_cons0.at:
  for +tt: List<&2, String>
  for +d: String
  for +t: List<&2, String>
  for b1: Bool
  for b2: Bool
  for w: &s: Nat -> {unsafe.miss(t, tt) == Nat.add(unsafe.miss(t, d <> tt), s) : Nat}
  exs s2: Nat
  {Bool.pick(Nat, b1, unsafe.miss(t, tt), 1n+unsafe.miss(t, tt))
    == Nat.add(Bool.pick(Nat, List.any.if(_u => b1, b2), unsafe.miss(t, d <> tt),
      1n+unsafe.miss(t, d <> tt)), s2) : Nat}

def unsafe.miss_cons0.at(tt, d, t, b1, b2, w):
  match b1:
    case True{}:
      match b2:
        case True{}:
          w
        case False{}:
          w
    case False{}:
      match b2:
        case True{}:
          unsafe.lift2(unsafe.miss(t, tt), unsafe.miss(t, d <> tt), w)
        case False{}:
          unsafe.lift1(unsafe.miss(t, tt), unsafe.miss(t, d <> tt), w)

# one path more in a list misses no more paths
law unsafe.miss_cons0:
  for rr: List<&2, String>
  for +tt: List<&2, String>
  for +d: String
  exs s: Nat
  {unsafe.miss(rr, tt) == Nat.add(unsafe.miss(rr, d <> tt), s) : Nat}

def unsafe.miss_cons0(rr, tt, d):
  match rr:
    case Nil{}:
      (0n, {==})
    case Con{+h, +t}:
      unsafe.miss_cons0.at(tt, d, t, Imports.has(tt, h), String.eq(d, h), unsafe.miss_cons0(t, tt, d))

# one path of rr against d, new to tt and among rr, on top of tt
law unsafe.miss_cons1.at:
  for +tt: List<&2, String>
  for +d: String
  for +h: String
  for +t: List<&2, String>
  for b1: Bool
  for b2: Bool
  for b3: Bool
  for e1: {Imports.has(tt, h) == b1 : Bool}
  for e2: {String.eq(d, h) == b2 : Bool}
  for e3: {String.eq(h, d) == b3 : Bool}
  for ht: {Imports.has(tt, d) == False{} : Bool}
  for hr: {List.any.if(_u => Imports.has(t, d), b3) == True{} : Bool}
  for ih: {Imports.has(t, d) == True{} : Bool}
    -> &s: Nat -> {unsafe.miss(t, tt) == 1n+Nat.add(unsafe.miss(t, d <> tt), s) : Nat}
  exs s2: Nat
  {Bool.pick(Nat, b1, unsafe.miss(t, tt), 1n+unsafe.miss(t, tt))
    == 1n+Nat.add(Bool.pick(Nat, List.any.if(_u => b1, b2), unsafe.miss(t, d <> tt),
      1n+unsafe.miss(t, d <> tt)), s2) : Nat}

def unsafe.miss_cons1.at(tt, d, h, t, b1, b2, b3, e1, e2, e3, ht, hr, ih):
  match b1:
    case True{}:
      match b2:
        case True{}:
          match b3:
            case True{}:
              ehd = Equal.cong(String, Bool, z => Imports.has(tt, z), h, d, M1.unsafe.seq(h, d, e3))
              Empty.absurd((&s2: Nat -> {unsafe.miss(t, tt) == 1n+Nat.add(unsafe.miss(t, d <> tt), s2) : Nat}),
                M1.unsafe.false_true(Equal.trans(Bool, False{}, Imports.has(tt, d), True{},
                  Equal.sym(Bool, Imports.has(tt, d), False{}, ht),
                  Equal.trans(Bool, Imports.has(tt, d), Imports.has(tt, h), True{},
                    Equal.sym(Bool, Imports.has(tt, h), Imports.has(tt, d), ehd), e1))))
            case False{}:
              ih(hr)
        case False{}:
          match b3:
            case True{}:
              ehd = Equal.cong(String, Bool, z => Imports.has(tt, z), h, d, M1.unsafe.seq(h, d, e3))
              Empty.absurd((&s2: Nat -> {unsafe.miss(t, tt) == 1n+Nat.add(unsafe.miss(t, d <> tt), s2) : Nat}),
                M1.unsafe.false_true(Equal.trans(Bool, False{}, Imports.has(tt, d), True{},
                  Equal.sym(Bool, Imports.has(tt, d), False{}, ht),
                  Equal.trans(Bool, Imports.has(tt, d), Imports.has(tt, h), True{},
                    Equal.sym(Bool, Imports.has(tt, h), Imports.has(tt, d), ehd), e1))))
            case False{}:
              ih(hr)
    case False{}:
      match b2:
        case True{}:
          unsafe.lift1(unsafe.miss(t, tt), unsafe.miss(t, d <> tt), unsafe.miss_cons0(t, tt, d))
        case False{}:
          match b3:
            case True{}:
              edh = Equal.cong(String, Bool, z => String.eq(d, z), h, d, M1.unsafe.seq(h, d, e3))
              Empty.absurd((&s2: Nat -> {1n+unsafe.miss(t, tt) == 1n+Nat.add(1n+unsafe.miss(t, d <> tt), s2) : Nat}),
                M1.unsafe.false_true(Equal.trans(Bool, False{}, String.eq(d, h), True{},
                  Equal.sym(Bool, String.eq(d, h), False{}, e2),
                  Equal.trans(Bool, String.eq(d, h), String.eq(d, d), True{}, edh, M2.unsafe.srefl(d)))))
            case False{}:
              unsafe.lift1(unsafe.miss(t, tt), 1n+unsafe.miss(t, d <> tt), ih(hr))

# a path of rr new to tt: one more in tt misses at least one path fewer
law unsafe.miss_cons1:
  for rr: List<&2, String>
  for +tt: List<&2, String>
  for +d: String
  for hr: {Imports.has(rr, d) == True{} : Bool}
  for +ht: {Imports.has(tt, d) == False{} : Bool}
  exs s: Nat
  {unsafe.miss(rr, tt) == 1n+Nat.add(unsafe.miss(rr, d <> tt), s) : Nat}

def unsafe.miss_cons1(rr, tt, d, hr, ht):
  match rr:
    case Nil{}:
      Empty.absurd((&s: Nat -> {unsafe.miss([], tt) == 1n+Nat.add(unsafe.miss([], d <> tt), s) : Nat}),
        M1.unsafe.false_true(hr))
    case Con{+h, +t}:
      unsafe.miss_cons1.at(tt, d, h, t, Imports.has(tt, h), String.eq(d, h), String.eq(h, d), {==}, {==}, {==}, ht, hr,
        z => unsafe.miss_cons1(t, tt, d, z, ht))

# the new path's count, with the rest's slack and one step's slack
law unsafe.fresh_count.new:
  for -mm: Nat
  for +ll: Nat
  for -mt: Nat
  for +m2: Nat
  for w: &s: Nat -> {mm == Nat.add(ll, Nat.add(mt, s)) : Nat}
  for v: &s: Nat -> {mt == 1n+Nat.add(m2, s) : Nat}
  exs s3: Nat
  {mm == 1n+Nat.add(ll, Nat.add(m2, s3)) : Nat}

def unsafe.fresh_count.new(mm, ll, mt, m2, w, v):
  (s1, e1) = w
  (s2, e2) = v
  +a1 = {s1 : Nat}
  +a2 = {s2 : Nat}
  (Nat.add(a2, a1), Equal.trans(Nat, mm, Nat.add(ll, Nat.add(1n+Nat.add(m2, a2), a1)), 1n+Nat.add(ll, Nat.add(m2,
    Nat.add(a2, a1))),
    Equal.trans(Nat, mm, Nat.add(ll, Nat.add(mt, a1)), Nat.add(ll, Nat.add(1n+Nat.add(m2, a2), a1)), e1,
      Equal.cong(Nat, Nat, z => Nat.add(ll, Nat.add(z, a1)), mt, 1n+Nat.add(m2, a2), e2)),
    Equal.trans(Nat, Nat.add(ll, 1n+Nat.add(Nat.add(m2, a2), a1)), 1n+Nat.add(ll, Nat.add(Nat.add(m2, a2), a1)),
      1n+Nat.add(ll, Nat.add(m2, Nat.add(a2, a1))), unsafe.add_succ(ll, Nat.add(Nat.add(m2, a2), a1)),
      Equal.cong(Nat, Nat, z => 1n+Nat.add(ll, z), Nat.add(Nat.add(m2, a2), a1), Nat.add(m2, Nat.add(a2, a1)),
        unsafe.add_assoc(m2, a2, a1)))))

# one import the walk looks at: taken up, it is new to the run's count
law unsafe.fresh_count.at:
  for +ds: List<&2, Digest.Digest>
  for +seen: List<&2, String>
  for +d: String
  for +more: List<&2, String>
  for b1: Bool
  for b2: Bool
  for b3: Bool
  for e1: {Imports.has(Imports.paths(Digest.edges(ds)), d) == b1 : Bool}
  for e2: {Imports.has(seen, d) == b2 : Bool}
  for e3: {Imports.has(more, d) == b3 : Bool}
  for w: &s: Nat -> {unsafe.miss(Imports.paths(Digest.edges(ds)), seen) == Nat.add(List.length(&2, String, more),
    Nat.add(unsafe.miss(Imports.paths(Digest.edges(ds)), List.append(&2, String, more, seen)), s)) : Nat}
  exs s2: Nat
  {unsafe.miss(Imports.paths(Digest.edges(ds)), seen)
    == Nat.add(List.length(&2, String, Bool.pick(List<&2, String>, Bool.and(Bool.and(b1, Bool.not(b2)), Bool.not(b3)),
      d <> more, more)), Nat.add(unsafe.miss(Imports.paths(Digest.edges(ds)), List.append(&2, String,
        Bool.pick(List<&2, String>, Bool.and(Bool.and(b1, Bool.not(b2)), Bool.not(b3)), d <> more, more), seen)), s2))
    : Nat}

def unsafe.fresh_count.at(ds, seen, d, more, b1, b2, b3, e1, e2, e3, w):
  match b1:
    case False{}:
      w
    case True{}:
      match b2:
        case True{}:
          w
        case False{}:
          match b3:
            case True{}:
              w
            case False{}:
              +rr = Imports.paths(Digest.edges(ds))
              +tt = List.append(&2, String, more, seen)
              ht = Equal.trans(Bool, Imports.has(tt, d), Bool.or(Imports.has(more, d), Imports.has(seen, d)), False{},
                unsafe.has_app(more, seen, d),
                Equal.trans(Bool, Bool.or(Imports.has(more, d), Imports.has(seen, d)), Imports.has(seen, d), False{},
                  Equal.cong(Bool, Bool, z => Bool.or(z, Imports.has(seen, d)), Imports.has(more, d), False{}, e3), e2))
              unsafe.fresh_count.new(unsafe.miss(rr, seen), List.length(&2, String, more), unsafe.miss(rr, tt),
                unsafe.miss(rr, d <> tt), w, unsafe.miss_cons1(rr, tt, d, e1, ht))

# the walk takes up only files new to what it has seen, each once: the
# count of read files not seen drops by at least as many
law unsafe.fresh_count:
  for +ds: List<&2, Digest.Digest>
  for xs: List<&2, String>
  for +seen: List<&2, String>
  exs s: Nat
  {unsafe.miss(Imports.paths(Digest.edges(ds)), seen)
    == Nat.add(List.length(&2, String, Imports.fresh.spec(xs, seen, Imports.paths(Digest.edges(ds)))),
      Nat.add(unsafe.miss(Imports.paths(Digest.edges(ds)), List.append(&2, String, Imports.fresh.spec(xs, seen,
        Imports.paths(Digest.edges(ds))), seen)), s)) : Nat}

def unsafe.fresh_count(ds, xs, seen):
  match xs:
    case Nil{}:
      +mm = unsafe.miss(Imports.paths(Digest.edges(ds)), seen)
      (0n, Equal.sym(Nat, Nat.add(mm, 0n), mm, unsafe.add_zero(mm)))
    case Con{+d, +rest}:
      +more = Imports.fresh.spec(rest, seen, Imports.paths(Digest.edges(ds)))
      unsafe.fresh_count.at(ds, seen, d, more, Imports.has(Imports.paths(Digest.edges(ds)), d), Imports.has(seen, d),
        Imports.has(more, d), {==}, {==}, {==}, unsafe.fresh_count(ds, rest, seen))

# a count moved along an equality
law unsafe.retarget:
  for -a: Nat
  for -b: Nat
  for -c: Nat
  for e: {a == b : Nat}
  for w: &k: Nat -> {b == 1n+Nat.add(c, k) : Nat}
  exs k2: Nat
  {a == 1n+Nat.add(c, k2) : Nat}

def unsafe.retarget(a, b, c, e, w):
  (k, ek) = w
  +k1 = {k : Nat}
  (k1, Equal.trans(Nat, a, b, 1n+Nat.add(c, k1), e, ek))

# a start that was read: the fuel covers it and every read file it has not
# seen
law unsafe.miss_start:
  for +ds: List<&2, Digest.Digest>
  for +a: String
  for hr: {Imports.has(Imports.paths(Digest.edges(ds)), a) == True{} : Bool}
  exs k: Nat
  {List.length(&2, Digest.Digest, ds) == 1n+Nat.add(unsafe.miss(Imports.paths(Digest.edges(ds)), [a]), k) : Nat}

def unsafe.miss_start(ds, a, hr):
  +rr = Imports.paths(Digest.edges(ds))
  unsafe.retarget(List.length(&2, Digest.Digest, ds), unsafe.miss(rr, []), unsafe.miss(rr, [a]),
    Equal.trans(Nat, List.length(&2, Digest.Digest, ds), List.length(&2, String, rr), unsafe.miss(rr, []),
      Equal.sym(Nat, List.length(&2, String, rr), List.length(&2, Digest.Digest, ds), unsafe.len_paths(ds)),
      Equal.sym(Nat, unsafe.miss(rr, []), List.length(&2, String, rr), unsafe.miss_nil(rr))),
    unsafe.miss_cons1(rr, [], a, hr, {==}))

# a step's fuel, moved to the next step: what the step takes up is paid for
# by what it newly sees
law unsafe.shut_walk.step:
  for -f: Nat
  for +l: Nat
  for -m: Nat
  for +k: Nat
  for +ff: Nat
  for -la: Nat
  for +m2: Nat
  for -m3: Nat
  for h1: {f == Nat.add(l, Nat.add(m, k)) : Nat}
  for w: &s: Nat -> {m == Nat.add(ff, Nat.add(m2, s)) : Nat}
  for h3: {la == Nat.add(ff, l) : Nat}
  for h4: {m3 == m2 : Nat}
  for -gg: Type
  for ih: @k2: Nat -> {f == Nat.add(la, Nat.add(m3, k2)) : Nat} -> gg
  gg

def unsafe.shut_walk.step(f, l, m, k, ff, la, m2, m3, h1, w, h3, h4, _gg, ih):
  (s, e) = w
  +s1 = {s : Nat}
  ih(Nat.add(s1, k), unsafe.count_arith(f, l, m, k, ff, la, m2, m3, s1, h1, e, h3, h4))

# the walk returns a shut list: while fuel lasts the invariant holds, and
# the fuel covers the worklist and every read file not yet seen, so it lasts
# until the worklist is empty
law unsafe.shut_walk:
  for +ds: List<&2, Digest.Digest>
  for fuel: Nat
  for todo: List<&2, String>
  for +seen: List<&2, String>
  for k: Nat
  for hf: {fuel == Nat.add(List.length(&2, String, todo), Nat.add(unsafe.miss(Imports.paths(Digest.edges(ds)), seen),
    k)) : Nat}
  for hi: {unsafe.inv(ds, todo, seen, seen) == True{} : Bool}
  {D1.unsafe.shut(ds, Imports.walk.spec(fuel, todo, seen, Digest.edges(ds), Imports.paths(Digest.edges(ds))),
    Imports.walk.spec(fuel, todo, seen, Digest.edges(ds), Imports.paths(Digest.edges(ds)))) == True{} : Bool}

def unsafe.shut_walk(ds, fuel, todo, seen, k, hf, hi):
  match fuel todo:
    case 0n Nil{}:
      Equal.trans(Bool, D1.unsafe.shut(ds, seen, seen), unsafe.inv(ds, [], seen, seen), True{},
        Equal.sym(Bool, unsafe.inv(ds, [], seen, seen), D1.unsafe.shut(ds, seen, seen), unsafe.inv_nil(ds, seen,
          seen)),
        hi)
    case 0n Con{_p, rest}:
      Empty.absurd({D1.unsafe.shut(ds, seen, seen) == True{} : Bool},
        unsafe.zero_succ(Nat.add(List.length(&2, String, rest), Nat.add(unsafe.miss(Imports.paths(Digest.edges(ds)),
          seen), k)), hf))
    case 1n+_f Nil{}:
      Equal.trans(Bool, D1.unsafe.shut(ds, seen, seen), unsafe.inv(ds, [], seen, seen), True{},
        Equal.sym(Bool, unsafe.inv(ds, [], seen, seen), D1.unsafe.shut(ds, seen, seen), unsafe.inv_nil(ds, seen,
          seen)),
        hi)
    case 1n+(+f) Con{+p, +rest}:
      +rr = Imports.paths(Digest.edges(ds))
      +deps = Imports.deps.spec(Digest.edges(ds), p)
      +found = Imports.fresh.spec(deps, seen, rr)
      +rf = List.reverse(&2, String, found)
      +seen2 = List.append(&2, String, rf, seen)
      +todo2 = List.append(&2, String, found, rest)
      +hg = unsafe.in_pre(rf, seen, seen, unsafe.in_refl(seen))
      hfs = unsafe.in_suf(rf, seen, found, Equal.trans(Bool, unsafe.all_in(rf, found), unsafe.all_in(found, found),
        True{}, unsafe.in_rev_set(found, found), unsafe.in_refl(found)))
      hd = unsafe.fresh_held(ds, seen2, deps, seen, hg, hfs)
      hp = Equal.trans(Bool, D1.unsafe.held(ds, seen2, D1.unsafe.imports(ds, p)), D1.unsafe.held(ds, seen2, deps),
        True{}, Equal.sym(Bool, D1.unsafe.held(ds, seen2, deps), D1.unsafe.held(ds, seen2,
          D1.unsafe.imports(ds, p)),
          Equal.cong(List<&2, String>, Bool, z => D1.unsafe.held(ds, seen2, z), deps, D1.unsafe.imports(ds, p),
            unsafe.deps_imports(ds, p))), hd)
      ha = unsafe.inv_todo(ds, todo2, seen2, rf, unsafe.in_rev(todo2, found, unsafe.in_suf(found, rest, found,
        unsafe.in_refl(found))))
      hb = unsafe.inv_keep(ds, p, rest, seen, found, seen2, seen, hp, hg, hi)
      +hi2 = unsafe.inv_app(ds, todo2, seen2, rf, seen, ha, hb)
      +mm = unsafe.miss(rr, seen)
      unsafe.shut_walk.step(f, List.length(&2, String, rest), mm, k, List.length(&2, String, found),
        List.length(&2, String, todo2), unsafe.miss(rr, List.append(&2, String, found, seen)), unsafe.miss(rr, seen2),
        unsafe.succ_inj(f, Nat.add(List.length(&2, String, rest), Nat.add(mm, k)), hf),
        unsafe.fresh_count(ds, deps, seen), unsafe.len_app(found, rest), unsafe.miss_rev(rr, found, seen),
        {D1.unsafe.shut(ds, Imports.walk.spec(f, todo2, seen2, Digest.edges(ds), rr),
          Imports.walk.spec(f, todo2, seen2, Digest.edges(ds), rr)) == True{} : Bool},
        k2 => h2 => unsafe.shut_walk(ds, f, todo2, seen2, k2, h2, hi2))

# a list shut over ps, held in another, leaves that one shut over ps
law unsafe.shut_grow:
  for +ds: List<&2, Digest.Digest>
  for +ss: List<&2, String>
  for +tt: List<&2, String>
  for ps: List<&2, String>
  for +h: {D1.unsafe.shut(ds, ss, ps) == True{} : Bool}
  for +hst: {unsafe.all_in(tt, ss) == True{} : Bool}
  {D1.unsafe.shut(ds, tt, ps) == True{} : Bool}

def unsafe.shut_grow(ds, ss, tt, ps, h, hst):
  match ps:
    case Nil{}:
      {==}
    case Con{+p, +t}:
      +hp = D1.unsafe.held(ds, ss, D1.unsafe.imports(ds, p))
      unsafe.and_true(D1.unsafe.held(ds, tt, D1.unsafe.imports(ds, p)), D1.unsafe.shut(ds, tt, t),
        unsafe.held_grow(ds, ss, tt, D1.unsafe.imports(ds, p), unsafe.and_l(hp, D1.unsafe.shut(ds, ss, t), h), hst),
        unsafe.shut_grow(ds, ss, tt, t, unsafe.and_r(hp, D1.unsafe.shut(ds, ss, t), h), hst))

# a list shut over ps is shut over any list that ps holds
law unsafe.shut_sub:
  for +ds: List<&2, Digest.Digest>
  for +ss: List<&2, String>
  for +ps: List<&2, String>
  for qs: List<&2, String>
  for +hs: {D1.unsafe.shut(ds, ss, ps) == True{} : Bool}
  for +hq: {unsafe.all_in(ps, qs) == True{} : Bool}
  {D1.unsafe.shut(ds, ss, qs) == True{} : Bool}

def unsafe.shut_sub(ds, ss, ps, qs, hs, hq):
  match qs:
    case Nil{}:
      {==}
    case Con{+q, +t}:
      unsafe.and_true(D1.unsafe.held(ds, ss, D1.unsafe.imports(ds, q)), D1.unsafe.shut(ds, ss, t),
        unsafe.shut_at(ds, ss, ps, q, hs, unsafe.and_l(Imports.has(ps, q), unsafe.all_in(ps, t), hq)),
        unsafe.shut_sub(ds, ss, ps, t, hs, unsafe.and_r(Imports.has(ps, q), unsafe.all_in(ps, t), hq)))

# one digest, of the path or not, when the path is not in the run
law unsafe.unread_imports.at:
  for -deps: List<&2, String>
  for -more: List<&2, String>
  for -rd: Bool
  for b: Bool
  for hr: {Bool.or(b, rd) == False{} : Bool}
  for ih: {rd == False{} : Bool} -> {more == [] : List<&2, String>}
  {Bool.pick(List<&2, String>, b, deps, more) == [] : List<&2, String>}

def unsafe.unread_imports.at(deps, _more, _rd, b, hr, ih):
  match b:
    case True{}:
      Empty.absurd({deps == [] : List<&2, String>}, M1.unsafe.false_true(Equal.sym(Bool, True{}, False{}, hr)))
    case False{}:
      ih(hr)

# a file not in the run imports nothing
law unsafe.unread_imports:
  for ds: List<&2, Digest.Digest>
  for +pp: String
  for h: {D1.unsafe.read(ds, pp) == False{} : Bool}
  {D1.unsafe.imports(ds, pp) == [] : List<&2, String>}

def unsafe.unread_imports(ds, pp, h):
  match ds:
    case Nil{}:
      {==}
    case Con{Digest.Digest{path, +norm, dir, is_laws, is_law_file, exempt, tops, says, deps, laws}, +rest}:
      unsafe.unread_imports.at(deps, D1.unsafe.imports(rest, pp), D1.unsafe.read(rest, pp), String.eq(norm, pp), h,
        z => unsafe.unread_imports(rest, pp, z))

# a walk with nothing to do returns what it has seen
law unsafe.idle:
  for +ds: List<&2, Digest.Digest>
  for fuel: Nat
  for +seen: List<&2, String>
  {Imports.walk.spec(fuel, [], seen, Digest.edges(ds), Imports.paths(Digest.edges(ds))) == seen : List<&2, String>}

def unsafe.idle(_ds, fuel, _seen):
  match fuel:
    case 0n:
      {==}
    case 1n+_f:
      {==}

# a start that imports nothing reaches only itself
law unsafe.lone_w:
  for +ds: List<&2, Digest.Digest>
  for fuel: Nat
  for +from: String
  for h: {Imports.deps.spec(Digest.edges(ds), from) == [] : List<&2, String>}
  {Imports.walk.spec(fuel, [from], [from], Digest.edges(ds), Imports.paths(Digest.edges(ds)))
    == [from] : List<&2, String>}

def unsafe.lone_w(ds, fuel, from, h):
  match fuel:
    case 0n:
      {==}
    case 1n+f:
      +rr = Imports.paths(Digest.edges(ds))
      %Equal.sym(List<&2, String>, Imports.deps.spec(Digest.edges(ds), from), [], h) :
        {Imports.walk.spec(f, List.append(&2, String, Imports.fresh.spec(_, [from], rr), []),
          List.append(&2, String, List.reverse(&2, String, Imports.fresh.spec(_, [from], rr)), [from]),
          Digest.edges(ds), rr)
          == [from] : List<&2, String>}
      unsafe.idle(ds, f, [from])

# a start that was read: the walk's fuel covers it
law unsafe.shut_top.go:
  for +ds: List<&2, Digest.Digest>
  for +from: String
  for w: &k: Nat -> {List.length(&2, Digest.Digest, ds)
    == 1n+Nat.add(unsafe.miss(Imports.paths(Digest.edges(ds)), [from]), k) : Nat}
  {D1.unsafe.shut(ds, Imports.walk.spec(List.length(&2, Digest.Digest, ds), [from], [from], Digest.edges(ds),
    Imports.paths(Digest.edges(ds))), Imports.walk.spec(List.length(&2, Digest.Digest, ds), [from], [from],
      Digest.edges(ds), Imports.paths(Digest.edges(ds)))) == True{} : Bool}

def unsafe.shut_top.go(ds, from, w):
  (k, e) = w
  +hh = D1.unsafe.held(ds, [from], D1.unsafe.imports(ds, from))
  unsafe.shut_walk(ds, List.length(&2, Digest.Digest, ds), [from], [from], k, e,
    unsafe.and_true(Bool.or(Imports.has([from], from), hh), True{},
      unsafe.or_l(Imports.has([from], from), hh,
        Equal.trans(Bool, Imports.has([from], from), Bool.or(String.eq(from, from), False{}), True{},
          unsafe.has_con(from, [], from), unsafe.or_l(String.eq(from, from), False{}, M2.unsafe.srefl(from)))),
        {==}))

# the walk from any start returns a shut list: a start that was read is
# covered by the fuel, and one that was not imports nothing
law unsafe.shut_top:
  for +ds: List<&2, Digest.Digest>
  for +from: String
  for b: Bool
  for eb: {Imports.has(Imports.paths(Digest.edges(ds)), from) == b : Bool}
  {D1.unsafe.shut(ds, Imports.walk.spec(List.length(&2, Digest.Digest, ds), [from], [from], Digest.edges(ds),
    Imports.paths(Digest.edges(ds))), Imports.walk.spec(List.length(&2, Digest.Digest, ds), [from], [from],
      Digest.edges(ds), Imports.paths(Digest.edges(ds)))) == True{} : Bool}

def unsafe.shut_top(ds, from, b, eb):
  match b:
    case True{}:
      unsafe.shut_top.go(ds, from, unsafe.miss_start(ds, from, eb))
    case False{}:
      +rr = Imports.paths(Digest.edges(ds))
      +ww = Imports.walk.spec(List.length(&2, Digest.Digest, ds), [from], [from], Digest.edges(ds), rr)
      er = Equal.trans(Bool, D1.unsafe.read(ds, from), Imports.has(rr, from), False{},
        Equal.sym(Bool, Imports.has(rr, from), D1.unsafe.read(ds, from), unsafe.read_paths(ds, from)), eb)
      +hn = unsafe.unread_imports(ds, from, er)
      hw = unsafe.lone_w(ds, List.length(&2, Digest.Digest, ds), from, Equal.trans(List<&2, String>,
        Imports.deps.spec(Digest.edges(ds), from), D1.unsafe.imports(ds, from),
        [], unsafe.deps_imports(ds, from), hn))
      %Equal.sym(List<&2, String>, ww, [from], hw) : {D1.unsafe.shut(ds, _, _) == True{} : Bool}
      %Equal.sym(List<&2, String>, D1.unsafe.imports(ds, from), [], hn) :
        {Bool.and(D1.unsafe.held(ds, [from], _), True{}) == True{} : Bool}
      {==}

def L1.unsafe_shut(ds, from):
  +ww = Imports.walk.spec(List.length(&2, Digest.Digest, ds), [from], [from], Digest.edges(ds),
    Imports.paths(Digest.edges(ds)))
  +rw = List.reverse(&2, String, ww)
  %Equal.sym(List<&2, String>, Imports.walk(List.length(&2, Digest.Digest, ds), [from], [from], Digest.edges(ds),
      Imports.paths(Digest.edges(ds))), ww, imp.closure(ds, from)) :
    {D1.unsafe.shut(ds, List.reverse(&2, String, _), List.reverse(&2, String, _)) == True{} : Bool}
  h = unsafe.shut_top(ds, from, Imports.has(Imports.paths(Digest.edges(ds)), from), {==})
  h2 = unsafe.shut_grow(ds, ww, rw, ww, h, Equal.trans(Bool, unsafe.all_in(rw, ww), unsafe.all_in(ww, ww), True{},
    unsafe.in_rev_set(ww, ww), unsafe.in_refl(ww)))
  unsafe.shut_sub(ds, rw, ww, rw, h2, unsafe.in_rev(ww, ww, unsafe.in_refl(ww)))
