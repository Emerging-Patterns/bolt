# taking one from a U32 and adding one to it undo each other
import Base
import ./UnsafeStringCompare.bend as M1
import ./InertTextFacts.bend as M2
import ./BinderIndex.bend as M3

# Word steps. A countdown of a line number (`U32.sub(n, 1)` until zero) and a
# count up to it (`U32.inc` from zero) meet at the same line: the two steps
# undo each other, on every word, with no bound to respect. `U32.sub(a, 1)`
# is an add of the complement with the carry set (Word.adc), so each fact is
# read off the low bit and carried up the word.

# adding the complement of zero with the carry set leaves a word as it is
law ws.keep:
  for n: Nat
  for w: Word(n)
  {Word.adc(n, w, Word.zero(n), True{}, True{}) == w : Word(n)}

def ws.keep(n, w):
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{False{}, +t}:
          Equal.cong(Word(p), Word(1n+p), z => WCon{False{}, z}, Word.adc(p, t, Word.zero(p), True{}, True{}), t,
            ws.keep(p, t))
        case WCon{True{}, +t}:
          Equal.cong(Word(p), Word(1n+p), z => WCon{True{}, z}, Word.adc(p, t, Word.zero(p), True{}, True{}), t,
            ws.keep(p, t))

# a borrow taken from a word just incremented gives the word back
law ws.back:
  for n: Nat
  for w: Word(n)
  {Word.adc(n, Word.inc(n, w), Word.zero(n), True{}, False{}) == w : Word(n)}

def ws.back(n, w):
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{False{}, +t}:
          Equal.cong(Word(p), Word(1n+p), z => WCon{False{}, z}, Word.adc(p, t, Word.zero(p), True{}, True{}), t,
            ws.keep(p, t))
        case WCon{True{}, +t}:
          Equal.cong(Word(p), Word(1n+p), z => WCon{True{}, z},
            Word.adc(p, Word.inc(p, t), Word.zero(p), True{}, False{}), t, ws.back(p, t))

# an increment after a borrow gives the word back
law ws.forth:
  for n: Nat
  for w: Word(n)
  {Word.inc(n, Word.adc(n, w, Word.zero(n), True{}, False{})) == w : Word(n)}

def ws.forth(n, w):
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{False{}, +t}:
          Equal.cong(Word(p), Word(1n+p), z => WCon{False{}, z},
            Word.inc(p, Word.adc(p, t, Word.zero(p), True{}, False{})), t, ws.forth(p, t))
        case WCon{True{}, +t}:
          Equal.cong(Word(p), Word(1n+p), z => WCon{True{}, z}, Word.adc(p, t, Word.zero(p), True{}, True{}), t,
            ws.keep(p, t))

# one taken from a word just incremented is the word
law ws.dec_inc:
  for p: Nat
  for w: Word(1n+p)
  {Word.adc(1n+p, Word.inc(1n+p, w), WCon{True{}, Word.zero(p)}, True{}, True{}) == w : Word(1n+p)}

def ws.dec_inc(p, w):
  match w:
    case WCon{False{}, +t}:
      Equal.cong(Word(p), Word(1n+p), z => WCon{False{}, z}, Word.adc(p, t, Word.zero(p), True{}, True{}), t,
        ws.keep(p, t))
    case WCon{True{}, +t}:
      Equal.cong(Word(p), Word(1n+p), z => WCon{True{}, z},
        Word.adc(p, Word.inc(p, t), Word.zero(p), True{}, False{}), t, ws.back(p, t))

# a word with one taken from it, incremented, is the word
law ws.inc_dec:
  for p: Nat
  for w: Word(1n+p)
  {Word.inc(1n+p, Word.adc(1n+p, w, WCon{True{}, Word.zero(p)}, True{}, True{})) == w : Word(1n+p)}

def ws.inc_dec(p, w):
  match w:
    case WCon{False{}, +t}:
      Equal.cong(Word(p), Word(1n+p), z => WCon{False{}, z},
        Word.inc(p, Word.adc(p, t, Word.zero(p), True{}, False{})), t, ws.forth(p, t))
    case WCon{True{}, +t}:
      Equal.cong(Word(p), Word(1n+p), z => WCon{True{}, z}, Word.adc(p, t, Word.zero(p), True{}, True{}), t,
        ws.keep(p, t))

# one taken from a U32 just incremented is that U32
law ws.down_up:
  for y: U32
  {U32.sub(U32.inc(y), 1) == y : U32}

def ws.down_up(y):
  match y:
    case U32{w}:
      Equal.cong(Word(32n), U32, z => U32{z},
        Word.adc(32n, Word.inc(32n, w), WCon{True{}, Word.zero(31n)}, True{}, True{}), w, ws.dec_inc(31n, w))

# a U32 with one taken from it, incremented, is that U32
law ws.up_down:
  for x: U32
  {U32.inc(U32.sub(x, 1)) == x : U32}

def ws.up_down(x):
  match x:
    case U32{w}:
      Equal.cong(Word(32n), U32, z => U32{z},
        Word.inc(32n, Word.adc(32n, w, WCon{True{}, Word.zero(31n)}, True{}, True{})), w, ws.inc_dec(31n, w))

# a U32 tests equal to itself
law ws.refl:
  for x: U32
  {U32.is_eq(x, x) == True{} : Bool}

def ws.refl(x):
  match x:
    case U32{+w}:
      %Equal.sym(Cmp, Word.cmp(32n, w, w), EQ{}, M1.unsafe.wrefl(32n, w)) : {Cmp.is_eq(_) == True{} : Bool}
      {==}

# two Bools each of which holds when the other does are the same Bool
law ws.iff:
  for p: Bool
  for q: Bool
  for f: {p == True{} : Bool} -> {q == True{} : Bool}
  for g: {q == True{} : Bool} -> {p == True{} : Bool}
  {p == q : Bool}

def ws.iff(p, q, f, g):
  match p q:
    case True{} True{}:
      {==}
    case True{} False{}:
      Equal.sym(Bool, False{}, True{}, f({==}))
    case False{} True{}:
      g({==})
    case False{} False{}:
      {==}

# equal U32s test equal
law ws.same:
  for +x: U32
  for -y: U32
  for e: {x == y : U32}
  {U32.is_eq(x, y) == True{} : Bool}

def ws.same(x, _yy, e):
  %e : {U32.is_eq(x, _) == True{} : Bool}
  ws.refl(x)

# U32s that test equal are equal
law ws.eq:
  for +x: U32
  for +y: U32
  for e: {U32.is_eq(x, y) == True{} : Bool}
  {x == y : U32}

def ws.eq(x, y, e):
  M2.inert.u32_eq(x, y, M3.ix.is_eq(U32.cmp(x, y), e))

# the test does not care which side is which
law ws.sym:
  for +x: U32
  for +y: U32
  {U32.is_eq(x, y) == U32.is_eq(y, x) : Bool}

def ws.sym(x, y):
  ws.iff(U32.is_eq(x, y), U32.is_eq(y, x),
    e => ws.same(y, x, Equal.sym(U32, x, y, ws.eq(x, y, e))),
    e => ws.same(x, y, Equal.sym(U32, y, x, ws.eq(y, x, e))))

# one taken from a U32 that leaves another: the U32 is that other incremented
law ws.shift.up:
  for +x: U32
  for -z: U32
  for e: {U32.sub(x, 1) == z : U32}
  {U32.is_eq(x, U32.inc(z)) == True{} : Bool}

def ws.shift.up(x, _zz, e):
  %e : {U32.is_eq(x, U32.inc(_)) == True{} : Bool}
  %Equal.sym(U32, U32.inc(U32.sub(x, 1)), x, ws.up_down(x)) : {U32.is_eq(x, _) == True{} : Bool}
  ws.refl(x)

# a U32 that is another incremented: one taken from it leaves that other
law ws.shift.down:
  for -x: U32
  for +z: U32
  for e: {x == U32.inc(z) : U32}
  {U32.is_eq(U32.sub(x, 1), z) == True{} : Bool}

def ws.shift.down(x, z, e):
  %Equal.sym(U32, x, U32.inc(z), e) : {U32.is_eq(U32.sub(_, 1), z) == True{} : Bool}
  %Equal.sym(U32, U32.sub(U32.inc(z), 1), z, ws.down_up(z)) : {U32.is_eq(_, z) == True{} : Bool}
  ws.refl(z)

# one taken from a U32 is another exactly when the U32 is that other
# incremented
law ws.shift:
  for +x: U32
  for +z: U32
  {U32.is_eq(U32.sub(x, 1), z) == U32.is_eq(x, U32.inc(z)) : Bool}

def ws.shift(x, z):
  ws.iff(U32.is_eq(U32.sub(x, 1), z), U32.is_eq(x, U32.inc(z)),
    e => ws.shift.up(x, z, ws.eq(U32.sub(x, 1), z, e)),
    e => ws.shift.down(x, z, ws.eq(x, U32.inc(z), e)))

# a U32 with one taken from it this many times
def ws.decn(k: Nat, nn: U32) -> U32:
  match k:
    case 0n:
      nn
    case 1n+p:
      U32.sub(ws.decn(p, nn), 1)

# a U32 incremented this many times
def ws.incn(k: Nat, y: U32) -> U32:
  match k:
    case 0n:
      y
    case 1n+p:
      ws.incn(p, U32.inc(y))

# a countdown reaches a U32 exactly when a count up from it reaches where
# the countdown began
law ws.meet:
  for k: Nat
  for +n: U32
  for +y: U32
  {U32.is_eq(ws.decn(k, n), y) == U32.is_eq(n, ws.incn(k, y)) : Bool}

def ws.meet(k, nn, y):
  match k:
    case 0n:
      {==}
    case 1n+(+p):
      Equal.trans(Bool, U32.is_eq(U32.sub(ws.decn(p, nn), 1), y), U32.is_eq(ws.decn(p, nn), U32.inc(y)),
        U32.is_eq(nn, ws.incn(p, U32.inc(y))), ws.shift(ws.decn(p, nn), y), ws.meet(p, nn, U32.inc(y)))

# an increment after a count up is the count up from an increment
law ws.incn_out:
  for k: Nat
  for +y: U32
  {U32.inc(ws.incn(k, y)) == ws.incn(k, U32.inc(y)) : U32}

def ws.incn_out(k, y):
  match k:
    case 0n:
      {==}
    case 1n+p:
      ws.incn_out(p, U32.inc(y))
