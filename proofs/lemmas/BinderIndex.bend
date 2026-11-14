# the binder's index of items answers as the scan of them does
import Base
import ../../src/syntax/bind.bend as Bind
import ../../src/lazy/lazy.bend as Lazy
import ../../laws/BinderIndexFindsItems.bend as L1
import ./InertTextFacts.bend as M1
import ./Put.bend as M2

# The index (laws/BinderIndexFindsItems.bend). A name goes down the low
# bits of its number to a leaf, and a lookup goes down the asked name's.
# Putting a name in changes a lookup only when the two numbers agree in
# those bits; two names the scan finds alike are the same name, so their
# numbers do agree, and the lookup then finds what the scan finds.

# a comparison that is_eq holds for is EQ
law ix.is_eq:
  for c: Cmp
  for e: {Cmp.is_eq(c) == True{} : Bool}
  {c == EQ{} : Cmp}

def ix.is_eq(c, e):
  match c:
    case LT{}:
      Empty.absurd({LT{} == EQ{} : Cmp}, M1.inert.false_true(e))
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({GT{} == EQ{} : Cmp}, M1.inert.false_true(e))

# the test of an early-exit and that holds holds
law ix.then_l:
  for a: Bool
  for -r: Bool
  for e: {Lazy.and_then(a, _u => r) == True{} : Bool}
  {a == True{} : Bool}

def ix.then_l(a, _r, e):
  match a:
    case True{}:
      {==}
    case False{}:
      e

# the rest of an early-exit and that holds holds
law ix.then_r:
  for a: Bool
  for -r: Bool
  for e: {Lazy.and_then(a, _u => r) == True{} : Bool}
  {r == True{} : Bool}

def ix.then_r(a, r, e):
  match a:
    case True{}:
      e
    case False{}:
      Empty.absurd({r == True{} : Bool}, M1.inert.false_true(e))

# two names the scan finds alike are the same name
law ix.same:
  for a: String
  for b: String
  for +e: {Bind.same(a, b) == True{} : Bool}
  {a == b : String}

def ix.same(a, b, e):
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{h, t}:
      Empty.absurd({SNil{} == SCon{h, t} : String}, M1.inert.false_true(e))
    case SCon{h, t} SNil{}:
      Empty.absurd({SCon{h, t} == SNil{} : String}, M1.inert.false_true(e))
    case SCon{Chr{+x}, +t1} SCon{Chr{+y}, +t2}:
      ex = M1.inert.u32_eq(x, y, ix.is_eq(U32.cmp(x, y), ix.then_l(U32.is_eq(x, y), Bind.same(t1, t2), e)))
      et = ix.same(t1, t2, ix.then_r(U32.is_eq(x, y), Bind.same(t1, t2), e))
      %ex : {SCon{Chr{x}, t1} == SCon{Chr{_}, t2} : String}
      %et : {SCon{Chr{x}, t1} == SCon{Chr{x}, _} : String}
      {==}

# two bits alike
def ix.bit(a: Bool, b: Bool) -> Bool:
  match a b:
    case True{} True{}:
      True{}
    case False{} False{}:
      True{}
    case x y:
      False{}

# two numbers alike in their low bits, this many of them
def ix.bits(d: Nat, +ka: U32, +kb: U32) -> Bool:
  match d:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(ix.bit(U32.is_even(ka), U32.is_even(kb)), ix.bits(p, U32.shr(ka), U32.shr(kb)))

# a bit is like itself
law ix.bit_refl:
  for b: Bool
  {ix.bit(b, b) == True{} : Bool}

def ix.bit_refl(b):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# a number is like itself in every bit
law ix.bits_refl:
  for d: Nat
  for +k: U32
  {ix.bits(d, k, k) == True{} : Bool}

def ix.bits_refl(d, k):
  match d:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Bool, ix.bit(U32.is_even(k), U32.is_even(k)), True{}, ix.bit_refl(U32.is_even(k))) :
        {Bool.and(_, ix.bits(p, U32.shr(k), U32.shr(k))) == True{} : Bool}
      ix.bits_refl(p, U32.shr(k))

# one level of the index: a lookup that goes down bit b2 past a put that went
# down bit b1 reads the put's half when the bits agree and the half the put
# left alone when they do not
law ix.step:
  for b1: Bool
  for b2: Bool
  for -sub: Bind.Index
  for -t: Bind.Index
  for -rest: Bool
  for -s: Bool
  for -hs: Bind.Index -> Bool
  for ih: {hs(sub) == Bool.or(Bool.and(rest, s), hs(Bind.index.near(b1, t))) : Bool}
  {hs(Bind.index.near(b2, Bind.index.join(b1, sub, Bind.index.near(Bool.not(b1), t))))
    == Bool.or(Bool.and(Bool.and(ix.bit(b1, b2), rest), s), hs(Bind.index.near(b2, t))) : Bool}

def ix.step(b1, b2, _sub, _tt, _rest, _ss, _hs, ih):
  match b1 b2:
    case True{} True{}:
      ih
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      ih

# a lookup after a put: the name put in, when the two numbers agree in the
# bits walked and the scan finds the names alike, or what was there before
law ix.put:
  for d: Nat
  for +k1: U32
  for +k2: U32
  for +t: Bind.Index
  for +nm: String
  for +name: String
  {Bind.index.has(d, k2, Bind.index.put(d, k1, t, nm), name)
    == Bool.or(Bool.and(ix.bits(d, k1, k2), Bind.same(nm, name)), Bind.index.has(d, k2, t, name)) : Bool}

def ix.put(d, k1, k2, t, nm, name):
  match d:
    case 0n:
      M2.put.or(Bind.same(nm, name), Bind.has_item(Bind.index.names(t), name),
        Bind.has_item(Bind.index.names(t), name), {==})
    case 1n+p:
      ix.step(U32.is_even(k1), U32.is_even(k2),
        Bind.index.put(p, U32.shr(k1), Bind.index.near(U32.is_even(k1), t), nm), t,
        ix.bits(p, U32.shr(k1), U32.shr(k2)), Bind.same(nm, name),
        x => Bind.index.has(p, U32.shr(k2), x, name),
        ix.put(p, U32.shr(k1), U32.shr(k2), Bind.index.near(U32.is_even(k1), t), nm, name))

# an and whose right side, when it holds, makes the left hold is its right
# side
law ix.guard:
  for sb: Bool
  for s: Bool
  for imp: {s == True{} : Bool} -> {sb == True{} : Bool}
  {Bool.and(sb, s) == s : Bool}

def ix.guard(sb, s, imp):
  match sb s:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      Empty.absurd({False{} == True{} : Bool}, M1.inert.false_true(imp({==})))
    case False{} False{}:
      {==}

# two names the scan finds alike have numbers alike in every bit walked
law ix.alike:
  for +nm: String
  for +name: String
  for +e: {Bind.same(nm, name) == True{} : Bool}
  {ix.bits(Bind.index.depth(), Bind.key(nm), Bind.key(name)) == True{} : Bool}

def ix.alike(nm, name, e):
  %ix.same(nm, name, e) : {ix.bits(Bind.index.depth(), Bind.key(nm), Bind.key(_)) == True{} : Bool}
  ix.bits_refl(Bind.index.depth(), Bind.key(nm))

def L1.index_finds(its, name):
  match its:
    case Nil{}:
      {==}
    case Con{+nm, +rest}:
      Equal.trans(Bool,
        Bind.indexed(Bind.index(nm <> rest), name),
        Bool.or(Bool.and(ix.bits(Bind.index.depth(), Bind.key(nm), Bind.key(name)), Bind.same(nm, name)),
          Bind.indexed(Bind.index(rest), name)),
        Lazy.or_else(Bind.same(nm, name), _u => Bind.has_item(rest, name)),
        ix.put(Bind.index.depth(), Bind.key(nm), Bind.key(name), Bind.index(rest), nm, name),
        Equal.trans(Bool,
          Bool.or(Bool.and(ix.bits(Bind.index.depth(), Bind.key(nm), Bind.key(name)), Bind.same(nm, name)),
            Bind.indexed(Bind.index(rest), name)),
          Bool.or(Bind.same(nm, name), Bind.indexed(Bind.index(rest), name)),
          Lazy.or_else(Bind.same(nm, name), _u => Bind.has_item(rest, name)),
          Equal.cong(Bool, Bool, z => Bool.or(z, Bind.indexed(Bind.index(rest), name)),
            Bool.and(ix.bits(Bind.index.depth(), Bind.key(nm), Bind.key(name)), Bind.same(nm, name)),
            Bind.same(nm, name),
            ix.guard(ix.bits(Bind.index.depth(), Bind.key(nm), Bind.key(name)), Bind.same(nm, name),
              e => ix.alike(nm, name, e))),
          Equal.sym(Bool, Lazy.or_else(Bind.same(nm, name), _u => Bind.has_item(rest, name)),
            Bool.or(Bind.same(nm, name), Bind.indexed(Bind.index(rest), name)),
            M2.put.or(Bind.same(nm, name), Bind.has_item(rest, name), Bind.indexed(Bind.index(rest), name),
              Equal.sym(Bool, Bind.indexed(Bind.index(rest), name), Bind.has_item(rest, name),
                L1.index_finds(rest, name))))))
