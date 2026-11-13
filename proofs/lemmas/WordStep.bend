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
  for yy: U32
  {U32.sub(U32.inc(yy), 1) == yy : U32}

def ws.down_up(yy):
  match yy:
    case U32{w}:
      Equal.cong(Word(32n), U32, z => U32{z},
        Word.adc(32n, Word.inc(32n, w), WCon{True{}, Word.zero(31n)}, True{}, True{}), w, ws.dec_inc(31n, w))

# a U32 with one taken from it, incremented, is that U32
law ws.up_down:
  for xx: U32
  {U32.inc(U32.sub(xx, 1)) == xx : U32}

def ws.up_down(xx):
  match xx:
    case U32{w}:
      Equal.cong(Word(32n), U32, z => U32{z},
        Word.inc(32n, Word.adc(32n, w, WCon{True{}, Word.zero(31n)}, True{}, True{})), w, ws.inc_dec(31n, w))

# a U32 tests equal to itself
law ws.refl:
  for xx: U32
  {U32.is_eq(xx, xx) == True{} : Bool}

def ws.refl(xx):
  match xx:
    case U32{+w}:
      %Equal.sym(Cmp, Word.cmp(32n, w, w), EQ{}, M1.unsafe.wrefl(32n, w)) : {Cmp.is_eq(_) == True{} : Bool}
      {==}

# two Bools each of which holds when the other does are the same Bool
law ws.iff:
  for pp: Bool
  for qq: Bool
  for ff: {pp == True{} : Bool} -> {qq == True{} : Bool}
  for gg: {qq == True{} : Bool} -> {pp == True{} : Bool}
  {pp == qq : Bool}

def ws.iff(pp, qq, ff, gg):
  match pp qq:
    case True{} True{}:
      {==}
    case True{} False{}:
      Equal.sym(Bool, False{}, True{}, ff({==}))
    case False{} True{}:
      gg({==})
    case False{} False{}:
      {==}

# equal U32s test equal
law ws.same:
  for +xx: U32
  for -yy: U32
  for e: {xx == yy : U32}
  {U32.is_eq(xx, yy) == True{} : Bool}

def ws.same(xx, _yy, e):
  %e : {U32.is_eq(xx, _) == True{} : Bool}
  ws.refl(xx)

# U32s that test equal are equal
law ws.eq:
  for +xx: U32
  for +yy: U32
  for e: {U32.is_eq(xx, yy) == True{} : Bool}
  {xx == yy : U32}

def ws.eq(xx, yy, e):
  M2.inert.u32_eq(xx, yy, M3.ix.is_eq(U32.cmp(xx, yy), e))

# the test does not care which side is which
law ws.sym:
  for +xx: U32
  for +yy: U32
  {U32.is_eq(xx, yy) == U32.is_eq(yy, xx) : Bool}

def ws.sym(xx, yy):
  ws.iff(U32.is_eq(xx, yy), U32.is_eq(yy, xx),
    e => ws.same(yy, xx, Equal.sym(U32, xx, yy, ws.eq(xx, yy, e))),
    e => ws.same(xx, yy, Equal.sym(U32, yy, xx, ws.eq(yy, xx, e))))

# one taken from a U32 that leaves another: the U32 is that other incremented
law ws.shift.up:
  for +xx: U32
  for -zz: U32
  for e: {U32.sub(xx, 1) == zz : U32}
  {U32.is_eq(xx, U32.inc(zz)) == True{} : Bool}

def ws.shift.up(xx, _zz, e):
  %e : {U32.is_eq(xx, U32.inc(_)) == True{} : Bool}
  %Equal.sym(U32, U32.inc(U32.sub(xx, 1)), xx, ws.up_down(xx)) : {U32.is_eq(xx, _) == True{} : Bool}
  ws.refl(xx)

# a U32 that is another incremented: one taken from it leaves that other
law ws.shift.down:
  for -xx: U32
  for +zz: U32
  for e: {xx == U32.inc(zz) : U32}
  {U32.is_eq(U32.sub(xx, 1), zz) == True{} : Bool}

def ws.shift.down(xx, zz, e):
  %Equal.sym(U32, xx, U32.inc(zz), e) : {U32.is_eq(U32.sub(_, 1), zz) == True{} : Bool}
  %Equal.sym(U32, U32.sub(U32.inc(zz), 1), zz, ws.down_up(zz)) : {U32.is_eq(_, zz) == True{} : Bool}
  ws.refl(zz)

# one taken from a U32 is another exactly when the U32 is that other
# incremented
law ws.shift:
  for +xx: U32
  for +zz: U32
  {U32.is_eq(U32.sub(xx, 1), zz) == U32.is_eq(xx, U32.inc(zz)) : Bool}

def ws.shift(xx, zz):
  ws.iff(U32.is_eq(U32.sub(xx, 1), zz), U32.is_eq(xx, U32.inc(zz)),
    e => ws.shift.up(xx, zz, ws.eq(U32.sub(xx, 1), zz, e)),
    e => ws.shift.down(xx, zz, ws.eq(xx, U32.inc(zz), e)))

# a U32 with one taken from it this many times
def ws.decn(kk: Nat, nn: U32) -> U32:
  match kk:
    case 0n:
      nn
    case 1n+p:
      U32.sub(ws.decn(p, nn), 1)

# a U32 incremented this many times
def ws.incn(kk: Nat, yy: U32) -> U32:
  match kk:
    case 0n:
      yy
    case 1n+p:
      ws.incn(p, U32.inc(yy))

# a countdown reaches a U32 exactly when a count up from it reaches where
# the countdown began
law ws.meet:
  for kk: Nat
  for +nn: U32
  for +yy: U32
  {U32.is_eq(ws.decn(kk, nn), yy) == U32.is_eq(nn, ws.incn(kk, yy)) : Bool}

def ws.meet(kk, nn, yy):
  match kk:
    case 0n:
      {==}
    case 1n+(+p):
      Equal.trans(Bool, U32.is_eq(U32.sub(ws.decn(p, nn), 1), yy), U32.is_eq(ws.decn(p, nn), U32.inc(yy)),
        U32.is_eq(nn, ws.incn(p, U32.inc(yy))), ws.shift(ws.decn(p, nn), yy), ws.meet(p, nn, U32.inc(yy)))

# an increment after a count up is the count up from an increment
law ws.incn_out:
  for kk: Nat
  for +yy: U32
  {U32.inc(ws.incn(kk, yy)) == ws.incn(kk, U32.inc(yy)) : U32}

def ws.incn_out(kk, yy):
  match kk:
    case 0n:
      {==}
    case 1n+p:
      ws.incn_out(p, U32.inc(yy))
