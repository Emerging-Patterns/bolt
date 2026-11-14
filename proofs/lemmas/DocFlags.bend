# doc's flags of the lines answer as its reading of the lines does
import Base
import ../../src/finding.bend as F
import ../../src/lazy/lazy.bend as Lazy
import ../../src/syntax/outline.bend as Outline
import ../../src/rules/style/doc.bend as Doc
import ../../laws/DocFlagsAnswerAsLines.bend as L1
import ./WordStep.bend as M1
import ./BinderIndex.bend as M2

# The flags (laws/DocFlagsAnswerAsLines.bend). check.lead counts a line
# number down to zero as it reads the lines; dl.up counts up from zero to
# the line number, and the two stop at the same line (WordStep's ws.meet).
# The flags are built counting up, each line put in after the ones below
# it, and a lookup after a put is that put's flag when the lines are the
# same, as the binder's index of names is exact.

# reading the lines down, counting up from i: does a comment block end
# right above line n?
def dl.up(lines: List<&2, String>, +i: U32, +n: U32, +ok: Bool) -> Bool:
  match lines:
    case Nil{}:
      Bool.and(U32.is_eq(i, n), ok)
    case Con{h, t}:
      Lazy.stop(Bool, U32.is_eq(i, n), ok, _u => dl.up(t, U32.inc(i), n, Doc.check.after(h, ok)))

# two early exits alike in their test and in what follows are alike
law dl.stop2:
  for -c1: Bool
  for -c2: Bool
  for -x: Bool
  for -y1: Bool
  for -y2: Bool
  for ec: {c1 == c2 : Bool}
  for ey: {y1 == y2 : Bool}
  {Lazy.stop(Bool, c1, x, _u => y1) == Lazy.stop(Bool, c2, x, _u => y2) : Bool}

def dl.stop2(c1, c2, x, y1, y2, ec, ey):
  Equal.trans(Bool, Lazy.stop(Bool, c1, x, _u => y1), Lazy.stop(Bool, c2, x, _u => y1),
    Lazy.stop(Bool, c2, x, _u => y2),
    Equal.cong(Bool, Bool, z => Lazy.stop(Bool, z, x, _u => y1), c1, c2, ec),
    Equal.cong(Bool, Bool, z => Lazy.stop(Bool, c2, x, _u => z), y1, y2, ey))

# the countdown is at zero exactly when the count up is at the line
law dl.cond:
  for +k: Nat
  for +n: U32
  {U32.is_eq(M1.ws.decn(k, n), 0) == U32.is_eq(M1.ws.incn(k, 0), n) : Bool}

def dl.cond(k, n):
  Equal.trans(Bool, U32.is_eq(M1.ws.decn(k, n), 0), U32.is_eq(n, M1.ws.incn(k, 0)),
    U32.is_eq(M1.ws.incn(k, 0), n), M1.ws.meet(k, n, 0), M1.ws.sym(n, M1.ws.incn(k, 0)))

# the rule's countdown, k lines in, reads as the count up k lines in
law dl.same:
  for lines: List<&2, String>
  for +k: Nat
  for +n: U32
  for +ok: Bool
  {Doc.check.lead(lines, M1.ws.decn(k, n), ok) == dl.up(lines, M1.ws.incn(k, 0), n, ok) : Bool}

def dl.same(lines, k, n, ok):
  match lines:
    case Nil{}:
      Equal.cong(Bool, Bool, z => Bool.and(z, ok), U32.is_eq(M1.ws.decn(k, n), 0),
        U32.is_eq(M1.ws.incn(k, 0), n), dl.cond(k, n))
    case Con{+h, +t}:
      dl.stop2(U32.is_eq(M1.ws.decn(k, n), 0), U32.is_eq(M1.ws.incn(k, 0), n), ok,
        Doc.check.lead(t, U32.sub(M1.ws.decn(k, n), 1), Doc.check.after(h, ok)),
        dl.up(t, U32.inc(M1.ws.incn(k, 0)), n, Doc.check.after(h, ok)),
        dl.cond(k, n),
        Equal.trans(Bool,
          Doc.check.lead(t, M1.ws.decn(Succ{k}, n), Doc.check.after(h, ok)),
          dl.up(t, M1.ws.incn(Succ{k}, 0), n, Doc.check.after(h, ok)),
          dl.up(t, U32.inc(M1.ws.incn(k, 0)), n, Doc.check.after(h, ok)),
          dl.same(t, Succ{k}, n, Doc.check.after(h, ok)),
          Equal.cong(U32, Bool, z => dl.up(t, z, n, Doc.check.after(h, ok)), M1.ws.incn(k, U32.inc(0)),
            U32.inc(M1.ws.incn(k, 0)),
            Equal.sym(U32, U32.inc(M1.ws.incn(k, 0)), M1.ws.incn(k, U32.inc(0)), M1.ws.incn_out(k, 0)))))

# one level of the flags: a lookup that goes down bit b2 past a put that went
# down bit b1 reads the put's half when the bits agree and the half the put
# left alone when they do not
law dl.level:
  for b1: Bool
  for b2: Bool
  for -sub: Doc.Flags
  for -fl: Doc.Flags
  for -rest: Bool
  for -m: Bool
  for -v: Bool
  for -fs: Doc.Flags -> Bool
  for ih: {fs(sub) == Bool.pick(Bool, Bool.and(rest, m), v, fs(Doc.flags.near(b1, fl))) : Bool}
  {fs(Doc.flags.near(b2, Doc.flags.join(b1, sub, Doc.flags.near(Bool.not(b1), fl))))
    == Bool.pick(Bool, Bool.and(Bool.and(M2.ix.bit(b1, b2), rest), m), v, fs(Doc.flags.near(b2, fl))) : Bool}

def dl.level(b1, b2, _sub, _fl, _rest, _mm, _vv, _fs, ih):
  match b1 b2:
    case True{} True{}:
      ih
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      ih

# an early exit is the pick it stands for
law dl.stop:
  for c: Bool
  for -a: Bool
  for -b: Bool
  {Lazy.stop(Bool, c, a, _u => b) == Bool.pick(Bool, c, a, b) : Bool}

def dl.stop(c, _aa, _bb):
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

# a lookup after a put: that cell's flag, when the two lines agree in the
# bits walked and the cell is at the line asked, or what was there before
law dl.put:
  for d: Nat
  for +k1: U32
  for +k2: U32
  for +fl: Doc.Flags
  for +l: U32
  for +v: Bool
  for +n: U32
  {Doc.flags.at(d, k2, Doc.flags.put(d, k1, fl, Doc.Cell{l, v}), n)
    == Bool.pick(Bool, Bool.and(M2.ix.bits(d, k1, k2), U32.is_eq(l, n)), v, Doc.flags.at(d, k2, fl, n))
    : Bool}

def dl.put(d, k1, k2, fl, l, v, nn):
  match d:
    case 0n:
      dl.stop(U32.is_eq(l, nn), v, Doc.flags.find(Doc.flags.cells(fl), nn))
    case 1n+(+p):
      dl.level(U32.is_even(k1), U32.is_even(k2),
        Doc.flags.put(p, U32.shr(k1), Doc.flags.near(U32.is_even(k1), fl), Doc.Cell{l, v}), fl,
        M2.ix.bits(p, U32.shr(k1), U32.shr(k2)), U32.is_eq(l, nn), v,
        x => Doc.flags.at(p, U32.shr(k2), x, nn),
        dl.put(p, U32.shr(k1), U32.shr(k2), Doc.flags.near(U32.is_even(k1), fl), l, v, nn))

# a cell at the line asked went down the way the lookup walks
law dl.alike:
  for +l: U32
  for +n: U32
  for e: {U32.is_eq(l, n) == True{} : Bool}
  {M2.ix.bits(Doc.flags.depth(), l, n) == True{} : Bool}

def dl.alike(l, n, e):
  %M1.ws.eq(l, n, e) : {M2.ix.bits(Doc.flags.depth(), l, _) == True{} : Bool}
  M2.ix.bits_refl(Doc.flags.depth(), l)

# a lookup after a line's cell is put in: that line's flag at that line,
# what was there before at any other
law dl.hit:
  for +l: U32
  for +v: Bool
  for +n: U32
  for +fl: Doc.Flags
  {Doc.above.at(Doc.flags.put(Doc.flags.depth(), l, fl, Doc.Cell{l, v}), n)
    == Bool.pick(Bool, U32.is_eq(l, n), v, Doc.above.at(fl, n)) : Bool}

def dl.hit(l, v, n, fl):
  Equal.trans(Bool,
    Doc.flags.at(Doc.flags.depth(), n, Doc.flags.put(Doc.flags.depth(), l, fl, Doc.Cell{l, v}), n),
    Bool.pick(Bool, Bool.and(M2.ix.bits(Doc.flags.depth(), l, n), U32.is_eq(l, n)), v,
      Doc.flags.at(Doc.flags.depth(), n, fl, n)),
    Bool.pick(Bool, U32.is_eq(l, n), v, Doc.flags.at(Doc.flags.depth(), n, fl, n)),
    dl.put(Doc.flags.depth(), l, n, fl, l, v, n),
    Equal.cong(Bool, Bool, z => Bool.pick(Bool, z, v, Doc.flags.at(Doc.flags.depth(), n, fl, n)),
      Bool.and(M2.ix.bits(Doc.flags.depth(), l, n), U32.is_eq(l, n)), U32.is_eq(l, n),
      M2.ix.guard(M2.ix.bits(Doc.flags.depth(), l, n), U32.is_eq(l, n), e => dl.alike(l, n, e))))

# a pick that falls to False is an and
law dl.and:
  for c: Bool
  for -x: Bool
  {Bool.pick(Bool, c, x, False{}) == Bool.and(c, x) : Bool}

def dl.and(c, _xx):
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

# the flags built counting up from a line answer as the count up from it
law dl.build:
  for lines: List<&2, String>
  for +i: U32
  for +n: U32
  for +ok: Bool
  {Doc.above.at(Doc.flags.build(lines, i, ok), n) == dl.up(lines, i, n, ok) : Bool}

def dl.build(lines, i, n, ok):
  match lines:
    case Nil{}:
      Equal.trans(Bool,
        Doc.above.at(Doc.flags.put(Doc.flags.depth(), i, Doc.FNone{}, Doc.Cell{i, ok}), n),
        Bool.pick(Bool, U32.is_eq(i, n), ok, Doc.above.at(Doc.FNone{}, n)),
        Bool.and(U32.is_eq(i, n), ok),
        dl.hit(i, ok, n, Doc.FNone{}),
        dl.and(U32.is_eq(i, n), ok))
    case Con{+h, +t}:
      +bt = Doc.flags.build(t, U32.inc(i), Doc.check.after(h, ok))
      +up = dl.up(t, U32.inc(i), n, Doc.check.after(h, ok))
      Equal.trans(Bool,
        Doc.above.at(Doc.flags.put(Doc.flags.depth(), i, bt, Doc.Cell{i, ok}), n),
        Bool.pick(Bool, U32.is_eq(i, n), ok, Doc.above.at(bt, n)),
        Lazy.stop(Bool, U32.is_eq(i, n), ok, _u => up),
        dl.hit(i, ok, n, bt),
        Equal.trans(Bool,
          Bool.pick(Bool, U32.is_eq(i, n), ok, Doc.above.at(bt, n)),
          Bool.pick(Bool, U32.is_eq(i, n), ok, up),
          Lazy.stop(Bool, U32.is_eq(i, n), ok, _u => up),
          Equal.cong(Bool, Bool, z => Bool.pick(Bool, U32.is_eq(i, n), ok, z), Doc.above.at(bt, n), up,
            dl.build(t, U32.inc(i), n, Doc.check.after(h, ok))),
          Equal.sym(Bool, Lazy.stop(Bool, U32.is_eq(i, n), ok, _u => up),
            Bool.pick(Bool, U32.is_eq(i, n), ok, up), dl.stop(U32.is_eq(i, n), ok, up))))

def L1.flags_answer(lines, nn):
  Equal.trans(Bool, Doc.above.at(Doc.flags(lines), nn), dl.up(lines, 0, nn, False{}), Doc.check.above(lines, nn),
    dl.build(lines, 0, nn, False{}),
    Equal.sym(Bool, Doc.check.above(lines, nn), dl.up(lines, 0, nn, False{}), dl.same(lines, 0n, nn, False{})))

def L1.fast_is_go(items, path, lines):
  match items:
    case Nil{}:
      {==}
    case Con{Outline.Item{+k, +name, +line, sig, doc, p}, +rest}:
      %Equal.sym(Bool, Doc.above.at(Doc.flags(lines), line), Doc.check.above(lines, line),
        L1.flags_answer(lines, line)) :
        {Bool.pick(List<&2, F.Finding>,
          Lazy.and_then(Bool.and(Doc.needs(k), Bool.not(Doc.exempt(name))), _u => Bool.not(_)),
          F.Finding{path, line, 0, 0, "doc", Doc.what(k) ++ " " ++ name ++ " has no comment above it."}
            <> Doc.check.fast(rest, path, Doc.flags(lines)),
          Doc.check.fast(rest, path, Doc.flags(lines)))
          == Doc.check.go(Outline.Item{k, name, line, sig, doc, p} <> rest, path, lines) : List<&2, F.Finding>}
      %Equal.sym(List<&2, F.Finding>, Doc.check.fast(rest, path, Doc.flags(lines)), Doc.check.go(rest, path, lines),
        L1.fast_is_go(rest, path, lines)) :
        {Bool.pick(List<&2, F.Finding>,
          Lazy.and_then(Bool.and(Doc.needs(k), Bool.not(Doc.exempt(name))),
            _u => Bool.not(Doc.check.above(lines, line))),
          F.Finding{path, line, 0, 0, "doc", Doc.what(k) ++ " " ++ name ++ " has no comment above it."} <> _, _)
          == Doc.check.go(Outline.Item{k, name, line, sig, doc, p} <> rest, path, lines) : List<&2, F.Finding>}
      {==}
