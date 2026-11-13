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

# reading the lines down, counting up from ii: does a comment block end
# right above line nn?
def dl.up(lines: List<&2, String>, +ii: U32, +nn: U32, +ok: Bool) -> Bool:
  match lines:
    case Nil{}:
      Bool.and(U32.is_eq(ii, nn), ok)
    case Con{hh, tt}:
      Lazy.stop(Bool, U32.is_eq(ii, nn), ok, _u => dl.up(tt, U32.inc(ii), nn, Doc.check.after(hh, ok)))

# two early exits alike in their test and in what follows are alike
law dl.stop2:
  for -c1: Bool
  for -c2: Bool
  for -xx: Bool
  for -y1: Bool
  for -y2: Bool
  for ec: {c1 == c2 : Bool}
  for ey: {y1 == y2 : Bool}
  {Lazy.stop(Bool, c1, xx, _u => y1) == Lazy.stop(Bool, c2, xx, _u => y2) : Bool}

def dl.stop2(c1, c2, xx, y1, y2, ec, ey):
  Equal.trans(Bool, Lazy.stop(Bool, c1, xx, _u => y1), Lazy.stop(Bool, c2, xx, _u => y1),
    Lazy.stop(Bool, c2, xx, _u => y2),
    Equal.cong(Bool, Bool, z => Lazy.stop(Bool, z, xx, _u => y1), c1, c2, ec),
    Equal.cong(Bool, Bool, z => Lazy.stop(Bool, c2, xx, _u => z), y1, y2, ey))

# the countdown is at zero exactly when the count up is at the line
law dl.cond:
  for +kk: Nat
  for +nn: U32
  {U32.is_eq(M1.ws.decn(kk, nn), 0) == U32.is_eq(M1.ws.incn(kk, 0), nn) : Bool}

def dl.cond(kk, nn):
  Equal.trans(Bool, U32.is_eq(M1.ws.decn(kk, nn), 0), U32.is_eq(nn, M1.ws.incn(kk, 0)),
    U32.is_eq(M1.ws.incn(kk, 0), nn), M1.ws.meet(kk, nn, 0), M1.ws.sym(nn, M1.ws.incn(kk, 0)))

# the rule's countdown, kk lines in, reads as the count up kk lines in
law dl.same:
  for lines: List<&2, String>
  for +kk: Nat
  for +nn: U32
  for +ok: Bool
  {Doc.check.lead(lines, M1.ws.decn(kk, nn), ok) == dl.up(lines, M1.ws.incn(kk, 0), nn, ok) : Bool}

def dl.same(lines, kk, nn, ok):
  match lines:
    case Nil{}:
      Equal.cong(Bool, Bool, z => Bool.and(z, ok), U32.is_eq(M1.ws.decn(kk, nn), 0),
        U32.is_eq(M1.ws.incn(kk, 0), nn), dl.cond(kk, nn))
    case Con{+hh, +tt}:
      dl.stop2(U32.is_eq(M1.ws.decn(kk, nn), 0), U32.is_eq(M1.ws.incn(kk, 0), nn), ok,
        Doc.check.lead(tt, U32.sub(M1.ws.decn(kk, nn), 1), Doc.check.after(hh, ok)),
        dl.up(tt, U32.inc(M1.ws.incn(kk, 0)), nn, Doc.check.after(hh, ok)),
        dl.cond(kk, nn),
        Equal.trans(Bool,
          Doc.check.lead(tt, M1.ws.decn(Succ{kk}, nn), Doc.check.after(hh, ok)),
          dl.up(tt, M1.ws.incn(Succ{kk}, 0), nn, Doc.check.after(hh, ok)),
          dl.up(tt, U32.inc(M1.ws.incn(kk, 0)), nn, Doc.check.after(hh, ok)),
          dl.same(tt, Succ{kk}, nn, Doc.check.after(hh, ok)),
          Equal.cong(U32, Bool, z => dl.up(tt, z, nn, Doc.check.after(hh, ok)), M1.ws.incn(kk, U32.inc(0)),
            U32.inc(M1.ws.incn(kk, 0)),
            Equal.sym(U32, U32.inc(M1.ws.incn(kk, 0)), M1.ws.incn(kk, U32.inc(0)), M1.ws.incn_out(kk, 0)))))

# one level of the flags: a lookup that goes down bit b2 past a put that went
# down bit b1 reads the put's half when the bits agree and the half the put
# left alone when they do not
law dl.level:
  for b1: Bool
  for b2: Bool
  for -sub: Doc.Flags
  for -fl: Doc.Flags
  for -rest: Bool
  for -mm: Bool
  for -vv: Bool
  for -fs: Doc.Flags -> Bool
  for ih: {fs(sub) == Bool.pick(Bool, Bool.and(rest, mm), vv, fs(Doc.flags.near(b1, fl))) : Bool}
  {fs(Doc.flags.near(b2, Doc.flags.join(b1, sub, Doc.flags.near(Bool.not(b1), fl))))
    == Bool.pick(Bool, Bool.and(Bool.and(M2.ix.bit(b1, b2), rest), mm), vv, fs(Doc.flags.near(b2, fl))) : Bool}

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
  for cc: Bool
  for -aa: Bool
  for -bb: Bool
  {Lazy.stop(Bool, cc, aa, _u => bb) == Bool.pick(Bool, cc, aa, bb) : Bool}

def dl.stop(cc, _aa, _bb):
  match cc:
    case True{}:
      {==}
    case False{}:
      {==}

# a lookup after a put: that cell's flag, when the two lines agree in the
# bits walked and the cell is at the line asked, or what was there before
law dl.put:
  for dd: Nat
  for +k1: U32
  for +k2: U32
  for +fl: Doc.Flags
  for +ll: U32
  for +vv: Bool
  for +nn: U32
  {Doc.flags.at(dd, k2, Doc.flags.put(dd, k1, fl, Doc.Cell{ll, vv}), nn)
    == Bool.pick(Bool, Bool.and(M2.ix.bits(dd, k1, k2), U32.is_eq(ll, nn)), vv, Doc.flags.at(dd, k2, fl, nn))
    : Bool}

def dl.put(dd, k1, k2, fl, ll, vv, nn):
  match dd:
    case 0n:
      dl.stop(U32.is_eq(ll, nn), vv, Doc.flags.find(Doc.flags.cells(fl), nn))
    case 1n+(+p):
      dl.level(U32.is_even(k1), U32.is_even(k2),
        Doc.flags.put(p, U32.shr(k1), Doc.flags.near(U32.is_even(k1), fl), Doc.Cell{ll, vv}), fl,
        M2.ix.bits(p, U32.shr(k1), U32.shr(k2)), U32.is_eq(ll, nn), vv,
        x => Doc.flags.at(p, U32.shr(k2), x, nn),
        dl.put(p, U32.shr(k1), U32.shr(k2), Doc.flags.near(U32.is_even(k1), fl), ll, vv, nn))

# a cell at the line asked went down the way the lookup walks
law dl.alike:
  for +ll: U32
  for +nn: U32
  for e: {U32.is_eq(ll, nn) == True{} : Bool}
  {M2.ix.bits(Doc.flags.depth(), ll, nn) == True{} : Bool}

def dl.alike(ll, nn, e):
  %M1.ws.eq(ll, nn, e) : {M2.ix.bits(Doc.flags.depth(), ll, _) == True{} : Bool}
  M2.ix.bits_refl(Doc.flags.depth(), ll)

# a lookup after a line's cell is put in: that line's flag at that line,
# what was there before at any other
law dl.hit:
  for +ll: U32
  for +vv: Bool
  for +nn: U32
  for +fl: Doc.Flags
  {Doc.above.at(Doc.flags.put(Doc.flags.depth(), ll, fl, Doc.Cell{ll, vv}), nn)
    == Bool.pick(Bool, U32.is_eq(ll, nn), vv, Doc.above.at(fl, nn)) : Bool}

def dl.hit(ll, vv, nn, fl):
  Equal.trans(Bool,
    Doc.flags.at(Doc.flags.depth(), nn, Doc.flags.put(Doc.flags.depth(), ll, fl, Doc.Cell{ll, vv}), nn),
    Bool.pick(Bool, Bool.and(M2.ix.bits(Doc.flags.depth(), ll, nn), U32.is_eq(ll, nn)), vv,
      Doc.flags.at(Doc.flags.depth(), nn, fl, nn)),
    Bool.pick(Bool, U32.is_eq(ll, nn), vv, Doc.flags.at(Doc.flags.depth(), nn, fl, nn)),
    dl.put(Doc.flags.depth(), ll, nn, fl, ll, vv, nn),
    Equal.cong(Bool, Bool, z => Bool.pick(Bool, z, vv, Doc.flags.at(Doc.flags.depth(), nn, fl, nn)),
      Bool.and(M2.ix.bits(Doc.flags.depth(), ll, nn), U32.is_eq(ll, nn)), U32.is_eq(ll, nn),
      M2.ix.guard(M2.ix.bits(Doc.flags.depth(), ll, nn), U32.is_eq(ll, nn), e => dl.alike(ll, nn, e))))

# a pick that falls to False is an and
law dl.and:
  for cc: Bool
  for -xx: Bool
  {Bool.pick(Bool, cc, xx, False{}) == Bool.and(cc, xx) : Bool}

def dl.and(cc, _xx):
  match cc:
    case True{}:
      {==}
    case False{}:
      {==}

# the flags built counting up from a line answer as the count up from it
law dl.build:
  for lines: List<&2, String>
  for +ii: U32
  for +nn: U32
  for +ok: Bool
  {Doc.above.at(Doc.flags.build(lines, ii, ok), nn) == dl.up(lines, ii, nn, ok) : Bool}

def dl.build(lines, ii, nn, ok):
  match lines:
    case Nil{}:
      Equal.trans(Bool,
        Doc.above.at(Doc.flags.put(Doc.flags.depth(), ii, Doc.FNone{}, Doc.Cell{ii, ok}), nn),
        Bool.pick(Bool, U32.is_eq(ii, nn), ok, Doc.above.at(Doc.FNone{}, nn)),
        Bool.and(U32.is_eq(ii, nn), ok),
        dl.hit(ii, ok, nn, Doc.FNone{}),
        dl.and(U32.is_eq(ii, nn), ok))
    case Con{+hh, +tt}:
      +bt = Doc.flags.build(tt, U32.inc(ii), Doc.check.after(hh, ok))
      +up = dl.up(tt, U32.inc(ii), nn, Doc.check.after(hh, ok))
      Equal.trans(Bool,
        Doc.above.at(Doc.flags.put(Doc.flags.depth(), ii, bt, Doc.Cell{ii, ok}), nn),
        Bool.pick(Bool, U32.is_eq(ii, nn), ok, Doc.above.at(bt, nn)),
        Lazy.stop(Bool, U32.is_eq(ii, nn), ok, _u => up),
        dl.hit(ii, ok, nn, bt),
        Equal.trans(Bool,
          Bool.pick(Bool, U32.is_eq(ii, nn), ok, Doc.above.at(bt, nn)),
          Bool.pick(Bool, U32.is_eq(ii, nn), ok, up),
          Lazy.stop(Bool, U32.is_eq(ii, nn), ok, _u => up),
          Equal.cong(Bool, Bool, z => Bool.pick(Bool, U32.is_eq(ii, nn), ok, z), Doc.above.at(bt, nn), up,
            dl.build(tt, U32.inc(ii), nn, Doc.check.after(hh, ok))),
          Equal.sym(Bool, Lazy.stop(Bool, U32.is_eq(ii, nn), ok, _u => up),
            Bool.pick(Bool, U32.is_eq(ii, nn), ok, up), dl.stop(U32.is_eq(ii, nn), ok, up))))

def L1.flags_answer(lines, nn):
  Equal.trans(Bool, Doc.above.at(Doc.flags(lines), nn), dl.up(lines, 0, nn, False{}), Doc.check.above(lines, nn),
    dl.build(lines, 0, nn, False{}),
    Equal.sym(Bool, Doc.check.above(lines, nn), dl.up(lines, 0, nn, False{}), dl.same(lines, 0n, nn, False{})))

def L1.fast_is_go(items, path, lines):
  match items:
    case Nil{}:
      {==}
    case Con{Outline.Item{+k, +name, +line, sig, doc, pp}, +rest}:
      %Equal.sym(Bool, Doc.above.at(Doc.flags(lines), line), Doc.check.above(lines, line),
        L1.flags_answer(lines, line)) :
        {Bool.pick(List<&2, F.Finding>,
          Lazy.and_then(Bool.and(Doc.needs(k), Bool.not(Doc.exempt(name))), _u => Bool.not(_)),
          F.Finding{path, line, 0, 0, "doc", Doc.what(k) ++ " " ++ name ++ " has no comment above it."}
            <> Doc.check.fast(rest, path, Doc.flags(lines)),
          Doc.check.fast(rest, path, Doc.flags(lines)))
          == Doc.check.go(Outline.Item{k, name, line, sig, doc, pp} <> rest, path, lines) : List<&2, F.Finding>}
      %Equal.sym(List<&2, F.Finding>, Doc.check.fast(rest, path, Doc.flags(lines)), Doc.check.go(rest, path, lines),
        L1.fast_is_go(rest, path, lines)) :
        {Bool.pick(List<&2, F.Finding>,
          Lazy.and_then(Bool.and(Doc.needs(k), Bool.not(Doc.exempt(name))),
            _u => Bool.not(Doc.check.above(lines, line))),
          F.Finding{path, line, 0, 0, "doc", Doc.what(k) ++ " " ++ name ++ " has no comment above it."} <> _, _)
          == Doc.check.go(Outline.Item{k, name, line, sig, doc, pp} <> rest, path, lines) : List<&2, F.Finding>}
      {==}
