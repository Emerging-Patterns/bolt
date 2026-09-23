# bolt/lsp: the proofs. `bend PROOF.bend` is the gate.
import Base
import 0xd9c8d4d2899ddda845dfa7525a3568ea/value.bend as J
import ./frame.bend as Frame
import ./server.bend as Server
import ../../lazy/lazy.bend as Lazy
import ./docs.bend as Docs
import ./report.bend as Rep
import ../finding.bend as F
import ../config.bend as Config
import ../rules.bend as Rules
import ../lint/world.bend as W
import ../lint/plan.bend as Plan
import ../src.bend as Src
import ./LAWS.bend as Laws

# small facts
# -----------

# the number before a successor
def pred(nn: Nat) -> Nat:
  match nn:
    case 0n:
      0n
    case 1n+p:
      p

# Unit for 0, Empty for a successor
def zero_ty(nn: Nat) -> Type:
  match nn:
    case 0n:
      Unit
    case 1n+p:
      Empty

# Unit for a successor, Empty for 0
def succ_ty(nn: Nat) -> Type:
  match nn:
    case 0n:
      Empty
    case 1n+p:
      Unit

# Unit for False, Empty for True
def false_ty(bb: Bool) -> Type:
  match bb:
    case False{}:
      Unit
    case True{}:
      Empty

# no successor is 0
law succ_zero:
  for -n: Nat
  for e: {1n+n == 0n : Nat}
  Empty

def succ_zero(_n, e):
  %e : succ_ty(_)
  Unit{}

# 0 is no successor
law zero_succ:
  for -n: Nat
  for e: {0n == 1n+n : Nat}
  Empty

def zero_succ(_n, e):
  %e : zero_ty(_)
  Unit{}

# False is never True
law false_true:
  for e: {False{} == True{} : Bool}
  Empty

def false_true(e):
  %e : false_ty(_)
  Unit{}

# True is never False
law true_false:
  for e: {True{} == False{} : Bool}
  Empty

def true_false(e):
  false_true(Equal.sym(Bool, True{}, False{}, e))

# n plus 0 is n
law add_zero:
  for n: Nat
  {Nat.add(n, 0n) == n : Nat}

def add_zero(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(p, 0n), p, add_zero(p))

# a successor on the right comes out front
law add_succ:
  for a: Nat
  for -b: Nat
  {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}

def add_succ(a, b):
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(p, 1n+b), 1n+Nat.add(p, b), add_succ(p, b))

# a list appended to nothing is itself
law app_nil:
  for -A: Data
  for xs: List<&2, A>
  {List.append(&2, A, xs, []) == xs : List<&2, A>}

def app_nil(A, xs):
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.cong(List<&2, A>, List<&2, A>, r => h <> r, List.append(&2, A, t, []), t, app_nil(A, t))

# appending is associative
law app_assoc:
  for -A: Data
  for xs: List<&2, A>
  for -ys: List<&2, A>
  for -zs: List<&2, A>
  {List.append(&2, A, List.append(&2, A, xs, ys), zs) == List.append(&2, A, xs, List.append(&2, A, ys, zs))
    : List<&2, A>}

def app_assoc(A, xs, ys, zs):
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.cong(List<&2, A>, List<&2, A>, r => h <> r, List.append(&2, A, List.append(&2, A, t, ys), zs),
        List.append(&2, A, t, List.append(&2, A, ys, zs)), app_assoc(A, t, ys, zs))

# reversing onto acc and then onto ys is acc reversed onto xs then ys
law rev_rev.go:
  for -A: Data
  for xs: List<&2, A>
  for acc: List<&2, A>
  for -ys: List<&2, A>
  {List.reverse.go(&2, A, List.reverse.go(&2, A, xs, acc), ys)
    == List.reverse.go(&2, A, acc, List.append(&2, A, xs, ys)) : List<&2, A>}

def rev_rev.go(A, xs, acc, ys):
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      rev_rev.go(A, t, h <> acc, ys)

# a list reversed twice is itself
law rev_rev:
  for -A: Data
  for xs: List<&2, A>
  {List.reverse(&2, A, List.reverse(&2, A, xs)) == xs : List<&2, A>}

def rev_rev(A, xs):
  +x2 = xs
  Equal.trans(List<&2, A>, List.reverse(&2, A, List.reverse(&2, A, x2)), List.append(&2, A, x2, []), x2,
    rev_rev.go(A, x2, [], []), app_nil(A, x2))

# reversing onto a list that is not empty gives one that is not empty
law rev_full:
  for -A: Data
  for xs: List<&2, A>
  for acc: List<&2, A>
  for h: {List.is_empty(&2, A, acc) == False{} : Bool}
  {List.is_empty(&2, A, List.reverse.go(&2, A, xs, acc)) == False{} : Bool}

def rev_full(A, xs, acc, h):
  match xs:
    case Nil{}:
      h
    case Con{x, t}:
      rev_full(A, t, x <> acc, {==})

# a list that is not empty reversed is not empty
law rev_full.of:
  for -A: Data
  for xs: List<&2, A>
  for h: {List.is_empty(&2, A, xs) == False{} : Bool}
  {List.is_empty(&2, A, List.reverse(&2, A, xs)) == False{} : Bool}

def rev_full.of(A, xs, h):
  match xs:
    case Nil{}:
      Empty.absurd({List.is_empty(&2, A, List.reverse(&2, A, Nil{})) == False{} : Bool}, true_false(h))
    case Con{x, t}:
      rev_full(A, t, [x], {==})

# counting
# --------

# n ticks onto a count
def ticks(nn: Nat, ds: List<&2, Frame.Digit>) -> List<&2, Frame.Digit>:
  match nn:
    case 0n:
      ds
    case 1n+p:
      ticks(p, Frame.tick(ds))

# the bytes of a char of any width, counted, are that many ticks
law count.char:
  for x: U32
  for rr: List<&2, U32>
  for ds: List<&2, Frame.Digit>
  for +b1: Bool
  for +b2: Bool
  for +b3: Bool
  {ticks(List.length(&2, U32, Frame.encode.char(Bool.pick(U32, b1, 1, Bool.pick(U32, b2, 2, Bool.pick(U32, b3, 3, 4))),
      x, rr)), ds)
    == ticks(List.length(&2, U32, rr), Frame.tick.by(Bool.pick(U32, b1, 1, Bool.pick(U32, b2, 2, Bool.pick(U32, b3, 3,
      4))), ds)) : List<&2, Frame.Digit>}

def count.char(_x, _rr, _ds, b1, b2, b3):
  match b1:
    case True{}:
      {==}
    case False{}:
      match b2:
        case True{}:
          {==}
        case False{}:
          match b3:
            case True{}:
              {==}
            case False{}:
              {==}

# byte_count ticks once for every byte UTF-8 takes
law count.bytes:
  for cs: List<&2, Char>
  for +ds: List<&2, Frame.Digit>
  {Frame.byte_count(cs, ds) == ticks(List.length(&2, U32, Frame.encode.go(cs)), ds) : List<&2, Frame.Digit>}

def count.bytes(cs, ds):
  match cs:
    case Nil{}:
      {==}
    case Con{c, +t}:
      +x = Char.to_u32(c)
      +w = Frame.width(x)
      Equal.trans(List<&2, Frame.Digit>, Frame.byte_count(t, Frame.tick.by(w, ds)),
        ticks(List.length(&2, U32, Frame.encode.go(t)), Frame.tick.by(w, ds)),
        ticks(List.length(&2, U32, Frame.encode.char(w, x, Frame.encode.go(t))), ds),
        count.bytes(t, Frame.tick.by(w, ds)),
        Equal.sym(List<&2, Frame.Digit>, ticks(List.length(&2, U32, Frame.encode.char(w, x, Frame.encode.go(t))), ds),
          ticks(List.length(&2, U32, Frame.encode.go(t)), Frame.tick.by(w, ds)),
          count.char(x, Frame.encode.go(t), ds, U32.is_lt(x, 128), U32.is_lt(x, 2048), U32.is_lt(x, 65536))))

# a tick adds one to the value
law count.tick:
  for ds: List<&2, Frame.Digit>
  {Laws.value(Frame.tick(ds)) == 1n+Laws.value(ds) : Nat}

def count.tick(ds):
  match ds:
    case Nil{}:
      {==}
    case Con{d, t}:
      match d:
        case Frame.D0{}:
          {==}
        case Frame.D1{}:
          {==}
        case Frame.D2{}:
          {==}
        case Frame.D3{}:
          {==}
        case Frame.D4{}:
          {==}
        case Frame.D5{}:
          {==}
        case Frame.D6{}:
          {==}
        case Frame.D7{}:
          {==}
        case Frame.D8{}:
          {==}
        case Frame.D9{}:
          Equal.cong(Nat, Nat, n => Laws.tens(n), Laws.value(Frame.tick(t)), 1n+Laws.value(t), count.tick(t))

# n ticks add n to the value
law count.ticks:
  for +nn: Nat
  for +ds: List<&2, Frame.Digit>
  {Laws.value(ticks(nn, ds)) == Nat.add(nn, Laws.value(ds)) : Nat}

def count.ticks(nn, ds):
  match nn:
    case 0n:
      {==}
    case 1n+p:
      +d2 = ds
      Equal.trans(Nat, Laws.value(ticks(p, Frame.tick(d2))), Nat.add(p, Laws.value(Frame.tick(d2))),
        1n+Nat.add(p, Laws.value(d2)),
        count.ticks(p, Frame.tick(d2)),
        Equal.trans(Nat, Nat.add(p, Laws.value(Frame.tick(d2))), Nat.add(p, 1n+Laws.value(d2)),
          1n+Nat.add(p, Laws.value(d2)),
          Equal.cong(Nat, Nat, n => Nat.add(p, n), Laws.value(Frame.tick(d2)), 1n+Laws.value(d2), count.tick(d2)),
          add_succ(p, Laws.value(d2))))

# the count of a string's bytes has their number for its value
law count.value:
  for +s: String
  {Laws.value(Frame.byte_count(String.to_list(s), [Frame.D0{}])) == List.length(&2, U32, Frame.encode(s)) : Nat}

def count.value(s):
  +n = List.length(&2, U32, Frame.encode(s))
  Equal.trans(Nat, Laws.value(Frame.byte_count(String.to_list(s), [Frame.D0{}])), Nat.add(n, 0n), n,
    Equal.trans(Nat, Laws.value(Frame.byte_count(String.to_list(s), [Frame.D0{}])),
      Laws.value(ticks(n, [Frame.D0{}])), Nat.add(n, 0n),
      Equal.cong(List<&2, Frame.Digit>, Nat, ds => Laws.value(ds), Frame.byte_count(String.to_list(s), [Frame.D0{}]),
        ticks(n, [Frame.D0{}]), count.bytes(String.to_list(s), [Frame.D0{}])),
      count.ticks(n, [Frame.D0{}])),
    add_zero(n))

# strings appended are associative
law str_assoc:
  for a: String
  for -b: String
  for -c: String
  {String.append(String.append(a, b), c) == String.append(a, String.append(b, c)) : String}

def str_assoc(a, b, c):
  match a:
    case SNil{}:
      {==}
    case SCon{h, t}:
      Equal.cong(String, String, r => SCon{h, r}, String.append(String.append(t, b), c),
        String.append(t, String.append(b, c)), str_assoc(t, b, c))

# a string with nothing appended is itself
law str_nil:
  for a: String
  {String.append(a, "") == a : String}

def str_nil(a):
  match a:
    case SNil{}:
      {==}
    case SCon{h, t}:
      Equal.cong(String, String, r => SCon{h, r}, String.append(t, ""), t, str_nil(t))

# a digit's code is its char
law digit.char:
  for dd: Frame.Digit
  {Char.from_u32(Frame.digit.code(dd)) == Laws.digit_char(dd) : Char}

def digit.char(dd):
  match dd:
    case Frame.D0{}:
      {==}
    case Frame.D1{}:
      {==}
    case Frame.D2{}:
      {==}
    case Frame.D3{}:
      {==}
    case Frame.D4{}:
      {==}
    case Frame.D5{}:
      {==}
    case Frame.D6{}:
      {==}
    case Frame.D7{}:
      {==}
    case Frame.D8{}:
      {==}
    case Frame.D9{}:
      {==}

# count.show writes a count's digits, most significant first, before acc
law count.show:
  for ds: List<&2, Frame.Digit>
  for +acc: String
  {Frame.count.show(ds, acc) == String.append(Laws.digits(ds), acc) : String}

def count.show(ds, acc):
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +t}:
      +fc = Char.from_u32(Frame.digit.code(d))
      +dc = Laws.digit_char(d)
      Equal.trans(String, Frame.count.show(t, SCon{fc, acc}), String.append(Laws.digits(t), SCon{fc, acc}),
        String.append(String.append(Laws.digits(t), SCon{dc, SNil{}}), acc),
        count.show(t, SCon{fc, acc}),
        Equal.trans(String, String.append(Laws.digits(t), SCon{fc, acc}), String.append(Laws.digits(t), SCon{dc, acc}),
          String.append(String.append(Laws.digits(t), SCon{dc, SNil{}}), acc),
          Equal.cong(Char, String, ch => String.append(Laws.digits(t), SCon{ch, acc}), fc, dc, digit.char(d)),
          Equal.sym(String, String.append(String.append(Laws.digits(t), SCon{dc, SNil{}}), acc),
            String.append(Laws.digits(t), SCon{dc, acc}), str_assoc(Laws.digits(t), SCon{dc, SNil{}}, acc))))

def Laws.frame_counts(s):
  +ds = Frame.byte_count(String.to_list(s), [Frame.D0{}])
  (ds, (Equal.cong(String, String, y => "Content-Length: " ++ y ++ "\r\n\r\n" ++ s, Frame.count.show(ds, ""),
    Laws.digits(ds), Equal.trans(String, Frame.count.show(ds, ""), String.append(Laws.digits(ds), ""), Laws.digits(ds),
      count.show(ds, ""), str_nil(Laws.digits(ds)))), count.value(s)))

# counting down
# -------------

# a count that is zero has value 0
law down.zero:
  for ds: List<&2, Frame.Digit>
  for h: {Frame.count.zero(ds) == True{} : Bool}
  {Laws.value(ds) == 0n : Nat}

def down.zero(ds, h):
  match ds:
    case Nil{}:
      {==}
    case Con{d, t}:
      match d:
        case Frame.D0{}:
          Equal.cong(Nat, Nat, n => Laws.tens(n), Laws.value(t), 0n, down.zero(t, h))
        case Frame.D1{}:
          Empty.absurd({Laws.value(Frame.D1{} <> t) == 0n : Nat}, false_true(h))
        case Frame.D2{}:
          Empty.absurd({Laws.value(Frame.D2{} <> t) == 0n : Nat}, false_true(h))
        case Frame.D3{}:
          Empty.absurd({Laws.value(Frame.D3{} <> t) == 0n : Nat}, false_true(h))
        case Frame.D4{}:
          Empty.absurd({Laws.value(Frame.D4{} <> t) == 0n : Nat}, false_true(h))
        case Frame.D5{}:
          Empty.absurd({Laws.value(Frame.D5{} <> t) == 0n : Nat}, false_true(h))
        case Frame.D6{}:
          Empty.absurd({Laws.value(Frame.D6{} <> t) == 0n : Nat}, false_true(h))
        case Frame.D7{}:
          Empty.absurd({Laws.value(Frame.D7{} <> t) == 0n : Nat}, false_true(h))
        case Frame.D8{}:
          Empty.absurd({Laws.value(Frame.D8{} <> t) == 0n : Nat}, false_true(h))
        case Frame.D9{}:
          Empty.absurd({Laws.value(Frame.D9{} <> t) == 0n : Nat}, false_true(h))

# a count that is not zero is one more than it untick'd
law down.untick:
  for ds: List<&2, Frame.Digit>
  for h: {Frame.count.zero(ds) == False{} : Bool}
  {Laws.value(ds) == 1n+Laws.value(Frame.untick(ds)) : Nat}

def down.untick(ds, h):
  match ds:
    case Nil{}:
      Empty.absurd({Laws.value(Nil{}) == 1n+Laws.value(Frame.untick(Nil{})) : Nat}, true_false(h))
    case Con{d, t}:
      match d:
        case Frame.D0{}:
          Equal.cong(Nat, Nat, n => Laws.tens(n), Laws.value(t), 1n+Laws.value(Frame.untick(t)), down.untick(t, h))
        case Frame.D1{}:
          {==}
        case Frame.D2{}:
          {==}
        case Frame.D3{}:
          {==}
        case Frame.D4{}:
          {==}
        case Frame.D5{}:
          {==}
        case Frame.D6{}:
          {==}
        case Frame.D7{}:
          {==}
        case Frame.D8{}:
          {==}
        case Frame.D9{}:
          {==}

# a count whose value is a successor is not zero (for b the count's zero test)
law down.full.go:
  for +ds: List<&2, Frame.Digit>
  for -n: Nat
  for b: Bool
  for hb: {Frame.count.zero(ds) == b : Bool}
  for +hv: {Laws.value(ds) == 1n+n : Nat}
  {Frame.count.zero(ds) == False{} : Bool}

def down.full.go(ds, n, b, hb, hv):
  match b:
    case True{}:
      Empty.absurd({Frame.count.zero(ds) == False{} : Bool},
        zero_succ(n, Equal.trans(Nat, 0n, Laws.value(ds), 1n+n,
          Equal.sym(Nat, Laws.value(ds), 0n, down.zero(ds, hb)), hv)))
    case False{}:
      hb

# a count whose value is a successor is not zero
law down.full:
  for +ds: List<&2, Frame.Digit>
  for -n: Nat
  for +hv: {Laws.value(ds) == 1n+n : Nat}
  {Frame.count.zero(ds) == False{} : Bool}

def down.full(ds, n, hv):
  down.full.go(ds, n, Frame.count.zero(ds), {==}, hv)

# a count whose value is 0 is zero (for b the count's zero test)
law down.empty.go:
  for +ds: List<&2, Frame.Digit>
  for b: Bool
  for hb: {Frame.count.zero(ds) == b : Bool}
  for hv: {Laws.value(ds) == 0n : Nat}
  {Frame.count.zero(ds) == True{} : Bool}

def down.empty.go(ds, b, hb, hv):
  match b:
    case True{}:
      hb
    case False{}:
      Empty.absurd({Frame.count.zero(ds) == True{} : Bool},
        succ_zero(Laws.value(Frame.untick(ds)), Equal.trans(Nat, 1n+Laws.value(Frame.untick(ds)), Laws.value(ds), 0n,
          Equal.sym(Nat, Laws.value(ds), 1n+Laws.value(Frame.untick(ds)), down.untick(ds, hb)), hv)))

# a count whose value is 0 is zero
law down.empty:
  for +ds: List<&2, Frame.Digit>
  for hv: {Laws.value(ds) == 0n : Nat}
  {Frame.count.zero(ds) == True{} : Bool}

def down.empty(ds, hv):
  down.empty.go(ds, Frame.count.zero(ds), {==}, hv)

# a count whose value is a successor, untick'd, has the value before it
law down.less:
  for +ds: List<&2, Frame.Digit>
  for -n: Nat
  for +hv: {Laws.value(ds) == 1n+n : Nat}
  {Laws.value(Frame.untick(ds)) == n : Nat}

def down.less(ds, n, hv):
  Equal.cong(Nat, Nat, m => pred(m), 1n+Laws.value(Frame.untick(ds)), 1n+n,
    Equal.trans(Nat, 1n+Laws.value(Frame.untick(ds)), Laws.value(ds), 1n+n,
      Equal.sym(Nat, Laws.value(ds), 1n+Laws.value(Frame.untick(ds)), down.untick(ds, down.full(ds, n, hv))), hv))

# split, once the count is zero, is ready
law split.ready:
  for zz: Bool
  for xs: List<&2, U32>
  for acc: List<&2, U32>
  for -more: Unit -> Frame.Cut
  for h: {zz == True{} : Bool}
  {Frame.split.on(zz, xs, acc, more) == Frame.Ready{List.reverse(&2, U32, acc), xs} : Frame.Cut}

def split.ready(zz, xs, acc, more, h):
  match zz:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({Frame.split.on(False{}, xs, acc, more) == Frame.Ready{List.reverse(&2, U32, acc), xs} : Frame.Cut},
        false_true(h))

# split, while the count is not zero, goes on
law split.more:
  for zz: Bool
  for -xs: List<&2, U32>
  for -acc: List<&2, U32>
  for more: Unit -> Frame.Cut
  for h: {zz == False{} : Bool}
  {Frame.split.on(zz, xs, acc, more) == more(Unit{}) : Frame.Cut}

def split.more(zz, xs, acc, more, h):
  match zz:
    case True{}:
      Empty.absurd({Frame.split.on(True{}, xs, acc, more) == more(Unit{}) : Frame.Cut}, true_false(h))
    case False{}:
      {==}

# split takes exactly as many bytes as the count's value
law split.takes:
  for xs: List<&2, U32>
  for +rest: List<&2, U32>
  for +ds: List<&2, Frame.Digit>
  for +acc: List<&2, U32>
  for +hv: {Laws.value(ds) == List.length(&2, U32, xs) : Nat}
  {Frame.split(List.append(&2, U32, xs, rest), ds, acc)
    == Frame.Ready{List.reverse(&2, U32, List.reverse.go(&2, U32, xs, acc)), rest} : Frame.Cut}

def split.takes(xs, rest, ds, acc, hv):
  match xs:
    case Nil{}:
      match rest:
        case Nil{}:
          split.ready(Frame.count.zero(ds), [], acc, _u => Frame.More{}, down.empty(ds, hv))
        case Con{+h, +t}:
          split.ready(Frame.count.zero(ds), h <> t, acc, _u => Frame.split(t, Frame.untick(ds), h <> acc),
            down.empty(ds, hv))
    case Con{+x, +t}:
      +tr = List.append(&2, U32, t, rest)
      Equal.trans(Frame.Cut, Frame.split(x <> tr, ds, acc), Frame.split(tr, Frame.untick(ds), x <> acc),
        Frame.Ready{List.reverse(&2, U32, List.reverse.go(&2, U32, t, x <> acc)), rest},
        split.more(Frame.count.zero(ds), x <> tr, acc, _u => Frame.split(tr, Frame.untick(ds), x <> acc),
          down.full(ds, List.length(&2, U32, t), hv)),
        split.takes(t, rest, Frame.untick(ds), x <> acc, down.less(ds, List.length(&2, U32, t), hv)))

# the wire
# --------

# digits, most significant first, as text in front of acc
def ms(dl: List<&2, Frame.Digit>, acc: String) -> String:
  match dl:
    case Nil{}:
      acc
    case Con{d, t}:
      SCon{Char.from_u32(Frame.digit.code(d)), ms(t, acc)}

# digits as their char codes
def codes(dl: List<&2, Frame.Digit>) -> List<&2, U32>:
  match dl:
    case Nil{}:
      Nil{}
    case Con{d, t}:
      Frame.digit.code(d) <> codes(t)

# bytes as chars, in order, in front of acc
def cmap(xs: List<&2, U32>, acc: List<&2, Char>) -> List<&2, Char>:
  match xs:
    case Nil{}:
      acc
    case Con{x, t}:
      Char.from_u32(x) <> cmap(t, acc)

# the bytes of "Content-Length: " in front of ys
def pfx(ys: List<&2, U32>) -> List<&2, U32>:
  67 <> 111 <> 110 <> 116 <> 101 <> 110 <> 116 <> 45 <> 76 <> 101 <> 110 <> 103 <> 116 <> 104 <> 58 <> 32 <> ys

# the header line once "Content-Length: " is read (reversed)
def pl() -> List<&2, U32>:
  [32, 58, 104, 116, 103, 110, 101, 76, 45, 116, 110, 101, 116, 110, 111, 67]

# the count wrap writes for s
def cnt(ss: String) -> List<&2, Frame.Digit>:
  Frame.byte_count(String.to_list(ss), [Frame.D0{}])

# that count's digits, most significant first
def msd(ss: String) -> List<&2, Frame.Digit>:
  List.reverse(&2, Frame.Digit, cnt(ss))

# the wire after "Content-Length: ", with zz after the blank line
def body(ss: String, zz: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, codes(msd(ss)), 13 <> 10 <> 13 <> 10 <> zz)

# count.show writes the digits reversed
law show.ms:
  for ds: List<&2, Frame.Digit>
  for dl: List<&2, Frame.Digit>
  for +acc: String
  {Frame.count.show(ds, ms(dl, acc)) == ms(List.reverse.go(&2, Frame.Digit, ds, dl), acc) : String}

def show.ms(ds, dl, acc):
  match ds:
    case Nil{}:
      {==}
    case Con{d, t}:
      show.ms(t, d <> dl, acc)

# text after digits goes after their tail
law ms.app:
  for dl: List<&2, Frame.Digit>
  for -x: String
  for -y: String
  {String.append(ms(dl, x), y) == ms(dl, String.append(x, y)) : String}

def ms.app(dl, x, y):
  match dl:
    case Nil{}:
      {==}
    case Con{d, t}:
      Equal.cong(String, String, r => SCon{Char.from_u32(Frame.digit.code(d)), r}, String.append(ms(t, x), y),
        ms(t, String.append(x, y)), ms.app(t, x, y))

# a digit takes one byte, its code
law enc.digit:
  for dd: Frame.Digit
  for -rr: List<&2, U32>
  {Frame.encode.one(Frame.digit.code(dd), rr) == Frame.digit.code(dd) <> rr : List<&2, U32>}

def enc.digit(dd, _rr):
  match dd:
    case Frame.D0{}:
      {==}
    case Frame.D1{}:
      {==}
    case Frame.D2{}:
      {==}
    case Frame.D3{}:
      {==}
    case Frame.D4{}:
      {==}
    case Frame.D5{}:
      {==}
    case Frame.D6{}:
      {==}
    case Frame.D7{}:
      {==}
    case Frame.D8{}:
      {==}
    case Frame.D9{}:
      {==}

# digits as text encode to their codes
law enc.ms:
  for dl: List<&2, Frame.Digit>
  for +acc: String
  {Frame.encode(ms(dl, acc)) == List.append(&2, U32, codes(dl), Frame.encode(acc)) : List<&2, U32>}

def enc.ms(dl, acc):
  match dl:
    case Nil{}:
      {==}
    case Con{+d, t}:
      Equal.trans(List<&2, U32>, Frame.encode.one(Frame.digit.code(d), Frame.encode(ms(t, acc))),
        Frame.digit.code(d) <> Frame.encode(ms(t, acc)),
        Frame.digit.code(d) <> List.append(&2, U32, codes(t), Frame.encode(acc)),
        enc.digit(d, Frame.encode(ms(t, acc))),
        Equal.cong(List<&2, U32>, List<&2, U32>, r => Frame.digit.code(d) <> r, Frame.encode(ms(t, acc)),
          List.append(&2, U32, codes(t), Frame.encode(acc)), enc.ms(t, acc)))

# the wire: "Content-Length: ", the count's digits, a blank line, the body
law wire.shape:
  for +s: String
  {Laws.wire(s) == pfx(body(s, Frame.encode(s))) : List<&2, U32>}

def wire.shape(s):
  +c = cnt(s)
  +dl = msd(s)
  +x = "\r\n\r\n" ++ s
  Equal.trans(List<&2, U32>, Laws.wire(s), Frame.encode(String.append("Content-Length: ", ms(dl, x))),
    pfx(body(s, Frame.encode(s))),
    Equal.trans(List<&2, U32>, Laws.wire(s),
      Frame.encode(String.append("Content-Length: ", String.append(ms(dl, ""), x))),
      Frame.encode(String.append("Content-Length: ", ms(dl, x))),
      Equal.cong(String, List<&2, U32>, y => Frame.encode("Content-Length: " ++ y ++ x), Frame.count.show(c, ""),
        ms(dl, ""), show.ms(c, [], "")),
      Equal.cong(String, List<&2, U32>, y => Frame.encode(String.append("Content-Length: ", y)),
        String.append(ms(dl, ""), x), ms(dl, x), ms.app(dl, "", x))),
    Equal.cong(List<&2, U32>, List<&2, U32>, y => pfx(y), Frame.encode(ms(dl, x)),
      List.append(&2, U32, codes(dl), Frame.encode(x)), enc.ms(dl, x)))

# the header steps over a digit
law hdr.digit:
  for dd: Frame.Digit
  for -t: List<&2, U32>
  for -line: List<&2, U32>
  for -len: List<&2, Frame.Digit>
  {Frame.header(Frame.digit.code(dd) <> t, line, len) == Frame.header(t, Frame.digit.code(dd) <> line, len)
    : Frame.Head}

def hdr.digit(dd, _t, _line, _len):
  match dd:
    case Frame.D0{}:
      {==}
    case Frame.D1{}:
      {==}
    case Frame.D2{}:
      {==}
    case Frame.D3{}:
      {==}
    case Frame.D4{}:
      {==}
    case Frame.D5{}:
      {==}
    case Frame.D6{}:
      {==}
    case Frame.D7{}:
      {==}
    case Frame.D8{}:
      {==}
    case Frame.D9{}:
      {==}

# the header steps over digits onto the line
law hdr.digits:
  for dl: List<&2, Frame.Digit>
  for +zz: List<&2, U32>
  for +line: List<&2, U32>
  for +len: List<&2, Frame.Digit>
  {Frame.header(List.append(&2, U32, codes(dl), zz), line, len)
    == Frame.header(zz, List.reverse.go(&2, U32, codes(dl), line), len) : Frame.Head}

def hdr.digits(dl, zz, line, len):
  match dl:
    case Nil{}:
      {==}
    case Con{+d, t}:
      Equal.trans(Frame.Head, Frame.header(Frame.digit.code(d) <> List.append(&2, U32, codes(t), zz), line, len),
        Frame.header(List.append(&2, U32, codes(t), zz), Frame.digit.code(d) <> line, len),
        Frame.header(zz, List.reverse.go(&2, U32, codes(t), Frame.digit.code(d) <> line), len),
        hdr.digit(d, List.append(&2, U32, codes(t), zz), line, len),
        hdr.digits(t, zz, Frame.digit.code(d) <> line, len))

# a newline ends a line that is not empty
law hdr.nl:
  for l: List<&2, U32>
  for -t: List<&2, U32>
  for -len: List<&2, Frame.Digit>
  for h: {List.is_empty(&2, U32, l) == False{} : Bool}
  {Frame.header(10 <> t, l, len) == Frame.header(t, [], Frame.line_len(l, len)) : Frame.Head}

def hdr.nl(l, t, len, h):
  match l:
    case Nil{}:
      Empty.absurd({Frame.header(10 <> t, Nil{}, len) == Frame.header(t, [], Frame.line_len(Nil{}, len)) : Frame.Head},
        true_false(h))
    case Con{x, r}:
      {==}

# chars of a line reversed onto ys
law chars.rg:
  for xs: List<&2, U32>
  for ys: List<&2, U32>
  for -acc: List<&2, Char>
  {Frame.chars(List.reverse.go(&2, U32, xs, ys), acc) == Frame.chars(ys, cmap(xs, acc)) : List<&2, Char>}

def chars.rg(xs, ys, acc):
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      chars.rg(t, x <> ys, acc)

# digit codes as chars are the digits as text
law fl.codes:
  for dl: List<&2, Frame.Digit>
  {String.from_list(cmap(codes(dl), [])) == ms(dl, SNil{}) : String}

def fl.codes(dl):
  match dl:
    case Nil{}:
      {==}
    case Con{d, t}:
      Equal.cong(String, String, r => SCon{Char.from_u32(Frame.digit.code(d)), r}, String.from_list(cmap(codes(t), [])),
        ms(t, SNil{}), fl.codes(t))

# reading digits as text pushes them onto the count
law read.ms:
  for dl: List<&2, Frame.Digit>
  for acc: List<&2, Frame.Digit>
  {Frame.count.read.go(ms(dl, SNil{}), Some{acc}) == Some{List.reverse.go(&2, Frame.Digit, dl, acc)}
    : Maybe<&2, List<&2, Frame.Digit>>}

def read.ms(dl, acc):
  match dl:
    case Nil{}:
      {==}
    case Con{d, t}:
      match d:
        case Frame.D0{}:
          read.ms(t, Frame.D0{} <> acc)
        case Frame.D1{}:
          read.ms(t, Frame.D1{} <> acc)
        case Frame.D2{}:
          read.ms(t, Frame.D2{} <> acc)
        case Frame.D3{}:
          read.ms(t, Frame.D3{} <> acc)
        case Frame.D4{}:
          read.ms(t, Frame.D4{} <> acc)
        case Frame.D5{}:
          read.ms(t, Frame.D5{} <> acc)
        case Frame.D6{}:
          read.ms(t, Frame.D6{} <> acc)
        case Frame.D7{}:
          read.ms(t, Frame.D7{} <> acc)
        case Frame.D8{}:
          read.ms(t, Frame.D8{} <> acc)
        case Frame.D9{}:
          read.ms(t, Frame.D9{} <> acc)

# the Content-Length line of digits reads back as them, reversed
law line.count:
  for dl: List<&2, Frame.Digit>
  for +len: List<&2, Frame.Digit>
  for h: {List.is_empty(&2, Frame.Digit, dl) == False{} : Bool}
  {Frame.line_len(List.reverse.go(&2, U32, codes(dl), pl()), len) == List.reverse(&2, Frame.Digit, dl)
    : List<&2, Frame.Digit>}

def line.count(dl, len, h):
  match dl:
    case Nil{}:
      Empty.absurd({Frame.line_len(List.reverse.go(&2, U32, codes(Nil{}), pl()), len)
        == List.reverse(&2, Frame.Digit, Nil{}) : List<&2, Frame.Digit>}, true_false(h))
    case Con{+d, +t}:
      +xs = codes(d <> t)
      Equal.trans(List<&2, Frame.Digit>, Frame.line_len(List.reverse.go(&2, U32, xs, pl()), len),
        Maybe.default(&2, List<&2, Frame.Digit>, Frame.count.read(ms(d <> t, SNil{})), len),
        List.reverse(&2, Frame.Digit, d <> t),
        Equal.trans(List<&2, Frame.Digit>, Frame.line_len(List.reverse.go(&2, U32, xs, pl()), len),
          Maybe.default(&2, List<&2, Frame.Digit>, Frame.count.read(String.from_list(cmap(xs, []))), len),
          Maybe.default(&2, List<&2, Frame.Digit>, Frame.count.read(ms(d <> t, SNil{})), len),
          Equal.cong(List<&2, Char>, List<&2, Frame.Digit>, +x => Bool.pick(List<&2, Frame.Digit>,
            String.starts_with(String.from_list(x), "Content-Length: "), Maybe.default(&2, List<&2, Frame.Digit>,
            Frame.count.read(String.drop(String.from_list(x), 16n)), len), len),
            Frame.chars(List.reverse.go(&2, U32, xs, pl()), []), Frame.chars(pl(), cmap(xs, [])),
            chars.rg(xs, pl(), [])),
          Equal.cong(String, List<&2, Frame.Digit>, y => Maybe.default(&2, List<&2, Frame.Digit>, Frame.count.read(y),
            len), String.from_list(cmap(xs, [])), ms(d <> t, SNil{}), fl.codes(d <> t))),
        Equal.cong(Maybe<&2, List<&2, Frame.Digit>>, List<&2, Frame.Digit>, m => Maybe.default(&2,
          List<&2, Frame.Digit>, m, len), Frame.count.read.go(ms(d <> t, SNil{}), Some{[]}),
          Some{List.reverse(&2, Frame.Digit, d <> t)}, read.ms(d <> t, [])))

# a tick is never empty
law tick.full:
  for ds: List<&2, Frame.Digit>
  {List.is_empty(&2, Frame.Digit, Frame.tick(ds)) == False{} : Bool}

def tick.full(ds):
  match ds:
    case Nil{}:
      {==}
    case Con{d, t}:
      match d:
        case Frame.D0{}:
          {==}
        case Frame.D1{}:
          {==}
        case Frame.D2{}:
          {==}
        case Frame.D3{}:
          {==}
        case Frame.D4{}:
          {==}
        case Frame.D5{}:
          {==}
        case Frame.D6{}:
          {==}
        case Frame.D7{}:
          {==}
        case Frame.D8{}:
          {==}
        case Frame.D9{}:
          {==}

# ticks onto a count that is not empty leave it not empty
law ticks.full:
  for nn: Nat
  for +ds: List<&2, Frame.Digit>
  for h: {List.is_empty(&2, Frame.Digit, ds) == False{} : Bool}
  {List.is_empty(&2, Frame.Digit, ticks(nn, ds)) == False{} : Bool}

def ticks.full(nn, ds, h):
  match nn:
    case 0n:
      h
    case 1n+p:
      ticks.full(p, Frame.tick(ds), tick.full(ds))

# the count wrap writes is never empty
law cnt.full:
  for +s: String
  {List.is_empty(&2, Frame.Digit, cnt(s)) == False{} : Bool}

def cnt.full(s):
  +n = List.length(&2, U32, Frame.encode(s))
  Equal.trans(Bool, List.is_empty(&2, Frame.Digit, cnt(s)), List.is_empty(&2, Frame.Digit, ticks(n, [Frame.D0{}])),
    False{},
    Equal.cong(List<&2, Frame.Digit>, Bool, x => List.is_empty(&2, Frame.Digit, x), cnt(s), ticks(n, [Frame.D0{}]),
      count.bytes(String.to_list(s), [Frame.D0{}])),
    ticks.full(n, [Frame.D0{}], {==}))

# the header line wrap writes reads back as its count
law line.cnt:
  for +s: String
  {Frame.line_len(List.reverse.go(&2, U32, codes(msd(s)), pl()), [Frame.D0{}]) == cnt(s) : List<&2, Frame.Digit>}

def line.cnt(s):
  Equal.trans(List<&2, Frame.Digit>, Frame.line_len(List.reverse.go(&2, U32, codes(msd(s)), pl()), [Frame.D0{}]),
    List.reverse(&2, Frame.Digit, msd(s)), cnt(s),
    line.count(msd(s), [Frame.D0{}], rev_full.of(Frame.Digit, cnt(s), cnt.full(s))),
    rev_rev(Frame.Digit, cnt(s)))

# the header wrap writes is read whole: its count, then what follows it
law head.shape:
  for +s: String
  for +zz: List<&2, U32>
  {Frame.header(body(s, zz), pl(), [Frame.D0{}]) == Frame.Head{cnt(s), zz} : Frame.Head}

def head.shape(s, zz):
  +l = List.reverse.go(&2, U32, codes(msd(s)), pl())
  Equal.trans(Frame.Head, Frame.header(body(s, zz), pl(), [Frame.D0{}]),
    Frame.header(13 <> 10 <> zz, [], Frame.line_len(l, [Frame.D0{}])), Frame.Head{cnt(s), zz},
    Equal.trans(Frame.Head, Frame.header(body(s, zz), pl(), [Frame.D0{}]),
      Frame.header(10 <> 13 <> 10 <> zz, l, [Frame.D0{}]),
      Frame.header(13 <> 10 <> zz, [], Frame.line_len(l, [Frame.D0{}])),
      hdr.digits(msd(s), 13 <> 10 <> 13 <> 10 <> zz, pl(), [Frame.D0{}]),
      hdr.nl(l, 13 <> 10 <> zz, [Frame.D0{}], rev_full(U32, codes(msd(s)), pl(), {==}))),
    Equal.cong(List<&2, Frame.Digit>, Frame.Head, n => Frame.Head{n, zz}, Frame.line_len(l, [Frame.D0{}]), cnt(s),
      line.cnt(s)))

def Laws.frame_round(s, more0):
  +more = more0
  +e = Frame.encode(s)
  Equal.trans(Frame.Cut, Frame.cut(List.append(&2, U32, Laws.wire(s), more)),
    Frame.split(List.append(&2, U32, e, more), cnt(s), []), Frame.Ready{e, more},
    Equal.trans(Frame.Cut, Frame.cut(List.append(&2, U32, Laws.wire(s), more)),
      Frame.cut.body(Frame.header(body(s, List.append(&2, U32, e, more)), pl(), [Frame.D0{}])),
      Frame.split(List.append(&2, U32, e, more), cnt(s), []),
      Equal.trans(Frame.Cut, Frame.cut(List.append(&2, U32, Laws.wire(s), more)),
        Frame.cut(List.append(&2, U32, pfx(body(s, e)), more)),
        Frame.cut.body(Frame.header(body(s, List.append(&2, U32, e, more)), pl(), [Frame.D0{}])),
        Equal.cong(List<&2, U32>, Frame.Cut, w => Frame.cut(List.append(&2, U32, w, more)), Laws.wire(s),
          pfx(body(s, e)), wire.shape(s)),
        Equal.cong(List<&2, U32>, Frame.Cut, y => Frame.cut.body(Frame.header(y, pl(), [Frame.D0{}])),
          List.append(&2, U32, body(s, e), more), body(s, List.append(&2, U32, e, more)),
          app_assoc(U32, codes(msd(s)), 13 <> 10 <> 13 <> 10 <> e, more))),
      Equal.cong(Frame.Head, Frame.Cut, hh => Frame.cut.body(hh),
        Frame.header(body(s, List.append(&2, U32, e, more)), pl(), [Frame.D0{}]),
        Frame.Head{cnt(s), List.append(&2, U32, e, more)}, head.shape(s, List.append(&2, U32, e, more)))),
    Equal.trans(Frame.Cut, Frame.split(List.append(&2, U32, e, more), cnt(s), []),
      Frame.Ready{List.reverse(&2, U32, List.reverse(&2, U32, e)), more}, Frame.Ready{e, more},
      split.takes(e, more, cnt(s), [], count.value(s)),
      Equal.cong(List<&2, U32>, Frame.Cut, x => Frame.Ready{x, more}, List.reverse(&2, U32, List.reverse(&2, U32, e)),
        e, rev_rev(U32, e))))

# waiting
# -------

# split waits on fewer bytes than the count's value
law split.waits:
  for xs: List<&2, U32>
  for +kk: Nat
  for +ds: List<&2, Frame.Digit>
  for +acc: List<&2, U32>
  for +hv: {Laws.value(ds) == List.length(&2, U32, xs) : Nat}
  for h: {Nat.is_lt(kk, List.length(&2, U32, xs)) == True{} : Bool}
  {Frame.split(List.take(&2, U32, xs, kk), ds, acc) == Frame.More{} : Frame.Cut}

def split.waits(xs, kk, ds, acc, hv, h):
  match xs:
    case Nil{}:
      match kk:
        case 0n:
          Empty.absurd({Frame.split(Nil{}, ds, acc) == Frame.More{} : Frame.Cut}, false_true(h))
        case 1n+p:
          Empty.absurd({Frame.split(Nil{}, ds, acc) == Frame.More{} : Frame.Cut}, false_true(h))
    case Con{+x, +t}:
      match kk:
        case 0n:
          split.more(Frame.count.zero(ds), [], acc, _u => Frame.More{}, down.full(ds, List.length(&2, U32, t), hv))
        case 1n+p:
          +tp = List.take(&2, U32, t, p)
          Equal.trans(Frame.Cut, Frame.split(x <> tp, ds, acc), Frame.split(tp, Frame.untick(ds), x <> acc),
            Frame.More{},
            split.more(Frame.count.zero(ds), x <> tp, acc, _u => Frame.split(tp, Frame.untick(ds), x <> acc),
              down.full(ds, List.length(&2, U32, t), hv)),
            split.waits(t, p, Frame.untick(ds), x <> acc, down.less(ds, List.length(&2, U32, t), hv), h))

# after the blank line's \r\n, a cut short of the body waits
law tail.waits.body:
  for +ee: List<&2, U32>
  for +jj: Nat
  for +len: List<&2, Frame.Digit>
  for +hv: {Laws.value(len) == List.length(&2, U32, ee) : Nat}
  for h: {Nat.is_lt(jj, 1n+1n+List.length(&2, U32, ee)) == True{} : Bool}
  {Frame.cut.body(Frame.header(List.take(&2, U32, 13 <> 10 <> ee, jj), [], len)) == Frame.More{} : Frame.Cut}

def tail.waits.body(ee, jj, len, hv, h):
  match jj:
    case 0n:
      {==}
    case 1n+j1:
      match j1:
        case 0n:
          {==}
        case 1n+j2:
          split.waits(ee, j2, len, [], hv, h)

# after the digits, a cut short of the body waits
law tail.waits:
  for +ee: List<&2, U32>
  for +jj: Nat
  for +l: List<&2, U32>
  for +len: List<&2, Frame.Digit>
  for hl: {List.is_empty(&2, U32, l) == False{} : Bool}
  for +hv: {Laws.value(Frame.line_len(l, len)) == List.length(&2, U32, ee) : Nat}
  for h: {Nat.is_lt(jj, List.length(&2, U32, 13 <> 10 <> 13 <> 10 <> ee)) == True{} : Bool}
  {Frame.cut.body(Frame.header(List.take(&2, U32, 13 <> 10 <> 13 <> 10 <> ee, jj), l, len)) == Frame.More{} : Frame.Cut}

def tail.waits(ee, jj, l, len, hl, hv, h):
  match jj:
    case 0n:
      {==}
    case 1n+j1:
      match j1:
        case 0n:
          {==}
        case 1n+j2:
          +tk = List.take(&2, U32, 13 <> 10 <> ee, j2)
          Equal.trans(Frame.Cut, Frame.cut.body(Frame.header(10 <> tk, l, len)),
            Frame.cut.body(Frame.header(tk, [], Frame.line_len(l, len))), Frame.More{},
            Equal.cong(Frame.Head, Frame.Cut, hh => Frame.cut.body(hh), Frame.header(10 <> tk, l, len),
              Frame.header(tk, [], Frame.line_len(l, len)), hdr.nl(l, tk, len, hl)),
            tail.waits.body(ee, j2, Frame.line_len(l, len), hv, h))

# a cut inside the digits waits; past them, it waits when the rest does
law digits.waits:
  for +dl: List<&2, Frame.Digit>
  for +zz: List<&2, U32>
  for +kk: Nat
  for +line: List<&2, U32>
  for +len: List<&2, Frame.Digit>
  for hz: @jj:Nat -> {Nat.is_lt(jj, List.length(&2, U32, zz)) == True{} : Bool}
    -> {Frame.cut.body(Frame.header(List.take(&2, U32, zz, jj), List.reverse.go(&2, U32, codes(dl), line), len))
      == Frame.More{} : Frame.Cut}
  for h: {Nat.is_lt(kk, List.length(&2, U32, List.append(&2, U32, codes(dl), zz))) == True{} : Bool}
  {Frame.cut.body(Frame.header(List.take(&2, U32, List.append(&2, U32, codes(dl), zz), kk), line, len)) == Frame.More{}
    : Frame.Cut}

def digits.waits(dl, zz, kk, line, len, hz, h):
  match dl:
    case Nil{}:
      hz(kk, h)
    case Con{+d, t}:
      match kk:
        case 0n:
          {==}
        case 1n+p:
          +tk = List.take(&2, U32, List.append(&2, U32, codes(t), zz), p)
          Equal.trans(Frame.Cut, Frame.cut.body(Frame.header(Frame.digit.code(d) <> tk, line, len)),
            Frame.cut.body(Frame.header(tk, Frame.digit.code(d) <> line, len)), Frame.More{},
            Equal.cong(Frame.Head, Frame.Cut, hh => Frame.cut.body(hh),
              Frame.header(Frame.digit.code(d) <> tk, line, len), Frame.header(tk, Frame.digit.code(d) <> line, len),
              hdr.digit(d, tk, line, len)),
            digits.waits(t, zz, p, Frame.digit.code(d) <> line, len, hz, h))

# a cut inside "Content-Length: " waits; past it, it waits when the rest does
law pfx.waits:
  for +ys: List<&2, U32>
  for +kk: Nat
  for hy: @jj:Nat -> {Nat.is_lt(jj, List.length(&2, U32, ys)) == True{} : Bool}
    -> {Frame.cut.body(Frame.header(List.take(&2, U32, ys, jj), pl(), [Frame.D0{}])) == Frame.More{} : Frame.Cut}
  for h: {Nat.is_lt(kk, List.length(&2, U32, pfx(ys))) == True{} : Bool}
  {Frame.cut(List.take(&2, U32, pfx(ys), kk)) == Frame.More{} : Frame.Cut}

def pfx.waits(_ys, kk, hy, h):
  match kk:
    case 0n:
      {==}
    case 1n+k1:
      match k1:
        case 0n:
          {==}
        case 1n+k2:
          match k2:
            case 0n:
              {==}
            case 1n+k3:
              match k3:
                case 0n:
                  {==}
                case 1n+k4:
                  match k4:
                    case 0n:
                      {==}
                    case 1n+k5:
                      match k5:
                        case 0n:
                          {==}
                        case 1n+k6:
                          match k6:
                            case 0n:
                              {==}
                            case 1n+k7:
                              match k7:
                                case 0n:
                                  {==}
                                case 1n+k8:
                                  match k8:
                                    case 0n:
                                      {==}
                                    case 1n+k9:
                                      match k9:
                                        case 0n:
                                          {==}
                                        case 1n+k10:
                                          match k10:
                                            case 0n:
                                              {==}
                                            case 1n+k11:
                                              match k11:
                                                case 0n:
                                                  {==}
                                                case 1n+k12:
                                                  match k12:
                                                    case 0n:
                                                      {==}
                                                    case 1n+k13:
                                                      match k13:
                                                        case 0n:
                                                          {==}
                                                        case 1n+k14:
                                                          match k14:
                                                            case 0n:
                                                              {==}
                                                            case 1n+k15:
                                                              match k15:
                                                                case 0n:
                                                                  {==}
                                                                case 1n+k16:
                                                                  hy(k16, h)

def Laws.frame_waits(s, kk0, h):
  +kk = kk0
  +e = Frame.encode(s)
  +w2 = pfx(body(s, e))
  +l = List.reverse.go(&2, U32, codes(msd(s)), pl())
  Equal.trans(Frame.Cut, Frame.cut(List.take(&2, U32, Laws.wire(s), kk)), Frame.cut(List.take(&2, U32, w2, kk)),
    Frame.More{},
    Equal.cong(List<&2, U32>, Frame.Cut, w => Frame.cut(List.take(&2, U32, w, kk)), Laws.wire(s), w2, wire.shape(s)),
    pfx.waits(body(s, e), kk,
      jj => hj => digits.waits(msd(s), 13 <> 10 <> 13 <> 10 <> e, jj, pl(), [Frame.D0{}],
        j2 => hj2 => tail.waits(e, j2, l, [Frame.D0{}], rev_full(U32, codes(msd(s)), pl(), {==}),
          Equal.trans(Nat, Laws.value(Frame.line_len(l, [Frame.D0{}])), Laws.value(cnt(s)), List.length(&2, U32, e),
            Equal.cong(List<&2, Frame.Digit>, Nat, x => Laws.value(x), Frame.line_len(l, [Frame.D0{}]), cnt(s),
              line.cnt(s)),
            count.value(s)),
          hj2),
        hj),
      Equal.trans(Bool, Nat.is_lt(kk, List.length(&2, U32, w2)), Nat.is_lt(kk, List.length(&2, U32, Laws.wire(s))),
        True{},
        Equal.cong(List<&2, U32>, Bool, w => Nat.is_lt(kk, List.length(&2, U32, w)), w2, Laws.wire(s),
          Equal.sym(List<&2, U32>, Laws.wire(s), w2, wire.shape(s))),
        h)))

# dispatch
# --------

# notifications carry no response ids
law notices_ids:
  for ns: List<&2, String>
  for -more: List<&2, Server.Reply>
  {Laws.ids(List.append(&2, Server.Reply, Server.notices(ns), more)) == Laws.ids(more) : List<&2, J.Json>}

def notices_ids(ns, more):
  match ns:
    case Nil{}:
      {==}
    case Con{n, t}:
      notices_ids(t, more)

# an unknown method's replies carry its id when it has one
law unknown_ids:
  for id: J.Json
  for -more: List<&2, Server.Reply>
  {Laws.ids(List.append(&2, Server.Reply, Server.unknown(id), more))
    == List.append(&2, J.Json, Laws.if_id(id), Laws.ids(more)) : List<&2, J.Json>}

def unknown_ids(id, _more):
  match id:
    case J.JNull{}:
      {==}
    case J.JBool{b}:
      {==}
    case J.JNum{raw}:
      {==}
    case J.JStr{s}:
      {==}
    case J.JArr{items}:
      {==}
    case J.JObj{pairs}:
      {==}
    case J.JNil{}:
      {==}
    case J.JCons{h, t}:
      {==}
    case J.JPair{k, v, r}:
      {==}
    case J.JSpan{src, n}:
      {==}
    case J.JBind{src, n, v, r}:
      {==}

# a response carries its request's id, a result or an error alike
law respond_ids:
  for -id: J.Json
  for aa: Server.Answer
  for -more: List<&2, Server.Reply>
  {Laws.ids(Server.respond(id, aa) <> more) == id <> Laws.ids(more) : List<&2, J.Json>}

def respond_ids(_id, aa, _more):
  match aa:
    case Server.Answer{r}:
      {==}
    case Server.Refusal{c, m}:
      {==}

# one message's replies carry the ids it is owed, then the rest's unless it
# was exit, whatever its work gave
law turn_ids:
  for w: Server.Work
  for mm: Server.Method
  for id: J.Json
  for -more: List<&2, Server.Reply>
  {Laws.ids(Laws.then(Server.step(mm, id, w), more)) == Laws.owed_all.go(mm, id, Laws.ids(more))
    : List<&2, J.Json>}

def turn_ids(w, mm, id, more):
  match w:
    case Server.Work{notes, answer, docs}:
      match mm:
        case Server.MInitialize{}:
          respond_ids(id, answer, more)
        case Server.MShutdown{}:
          respond_ids(id, answer, more)
        case Server.MExit{}:
          {==}
        case Server.MOpen{}:
          notices_ids(notes, more)
        case Server.MChange{}:
          notices_ids(notes, more)
        case Server.MSave{}:
          notices_ids(notes, more)
        case Server.MClose{}:
          notices_ids(notes, more)
        case Server.MHover{}:
          respond_ids(id, answer, more)
        case Server.MDefinition{}:
          respond_ids(id, answer, more)
        case Server.MSymbols{}:
          respond_ids(id, answer, more)
        case Server.MCompletion{}:
          respond_ids(id, answer, more)
        case Server.MReferences{}:
          respond_ids(id, answer, more)
        case Server.MRename{}:
          respond_ids(id, answer, more)
        case Server.MSemantic{}:
          respond_ids(id, answer, more)
        case Server.MOther{}:
          unknown_ids(id, more)

def Laws.replies_pair(ts):
  match ts:
    case Nil{}:
      {==}
    case Con{tt, rest}:
      match tt:
        case Laws.Turn{+msg, w}:
          +mm = Server.method(Server.name_of(msg))
          +id = Server.id_of(msg)
          Equal.trans(List<&2, J.Json>, Laws.ids(Laws.then(Server.step(mm, id, w), Laws.replies(rest))),
            Laws.owed_all.go(mm, id, Laws.ids(Laws.replies(rest))), Laws.owed_all.go(mm, id, Laws.owed_all(rest)),
            turn_ids(w, mm, id, Laws.replies(rest)),
            Equal.cong(List<&2, J.Json>, List<&2, J.Json>, x => Laws.owed_all.go(mm, id, x),
              Laws.ids(Laws.replies(rest)), Laws.owed_all(rest), Laws.replies_pair(rest)))

# the method the server does not know is refused with the id, or ignored
# without one, whatever its work gave
law unknown_other:
  for w: Server.Work
  for id: J.Json
  {Laws.sent(Server.step(Server.MOther{}, id, w)) == Laws.refusal(id) : List<&2, Server.Reply>}

def unknown_other(w, id):
  match w:
    case Server.Work{notes, answer, docs}:
      match id:
        case J.JNull{}:
          {==}
        case J.JBool{b}:
          {==}
        case J.JNum{raw}:
          {==}
        case J.JStr{s}:
          {==}
        case J.JArr{items}:
          {==}
        case J.JObj{pairs}:
          {==}
        case J.JNil{}:
          {==}
        case J.JCons{h, t}:
          {==}
        case J.JPair{k, v, r}:
          {==}
        case J.JSpan{src, n}:
          {==}
        case J.JBind{src, n, v, r}:
          {==}

def Laws.unknown_refused(name, h, id, w):
  Equal.trans(List<&2, Server.Reply>, Laws.sent(Server.step(Server.method(name), id, w)),
    Laws.sent(Server.step(Server.MOther{}, id, w)), Laws.refusal(id),
    Equal.cong(Server.Method, List<&2, Server.Reply>, m => Laws.sent(Server.step(m, id, w)), Server.method(name),
      Server.MOther{}, h),
    unknown_other(w, id))


# Publishing (BOLT-LSP-2, BOLT-LSP-4). The documents are looked up by
# String.eq, so the keep laws need it to be reflexive; that goes down to the
# words a U32 is made of. The CLI side walks the planner's run over one named
# file, cased on whether that file is a bolt.bend.

# a bit compares equal to itself
law pub.bcmp:
  for b: Bool
  {Bool.cmp(b, b) == EQ{} : Cmp}

def pub.bcmp(b):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# a word compares equal to itself
law pub.weq_refl:
  for n: Nat
  for a: Word(n)
  {Word.cmp(n, a, a) == EQ{} : Cmp}

def pub.weq_refl(n, a):
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      match a:
        case WCon{b, +t}:
          e = Equal.sym(Cmp, Word.cmp(p, t, t), EQ{}, pub.weq_refl(p, t))
          %e : {Word.cmp.fin(b, b, _) == EQ{} : Cmp}
          pub.bcmp(b)

# a compare that went on past equal first characters answers as the rest's
law pub.rec:
  for -h1: Char
  for -h2: Char
  for rr: (String & String) & Cmp
  {String.eq.fin(String.cmp.rec(h1, h2, rr)) == String.eq.fin(rr) : Bool}

def pub.rec(_h1, _h2, rr):
  ((_a, _b), _c) = rr
  {==}

# a string is equal to itself
law pub.seq_refl:
  for s: String
  {String.eq(s, s) == True{} : Bool}

def pub.seq_refl(s):
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{U32{+w}}, +t}:
      e = Equal.sym(Cmp, Word.cmp(32n, w, w), EQ{}, pub.weq_refl(32n, w))
      %e : {String.eq.fin(String.cmp.fin(t, t, ((Chr{U32{w}}, Chr{U32{w}}), _))) == True{} : Bool}
      Equal.trans(Bool, String.eq.fin(String.cmp.rec(Chr{U32{w}}, Chr{U32{w}}, String.cmp(t, t))),
        String.eq(t, t), True{}, pub.rec(Chr{U32{w}}, Chr{U32{w}}, String.cmp(t, t)), pub.seq_refl(t))

# the document just put at the head of the list is the one a lookup of its
# URI finds: its errors
law pub.errors_head:
  for +uri: String
  for -text: String
  for -ds: List<&2, Rep.Diag>
  for -rest: List<&2, Docs.Doc>
  {Docs.errors(Docs.Doc{uri, text, ds} <> rest, uri) == ds : List<&2, Rep.Diag>}

def pub.errors_head(uri, _text, ds, rest):
  e = Equal.sym(Bool, String.eq(uri, uri), True{}, pub.seq_refl(uri))
  %e : {Lazy.stop(List<&2, Rep.Diag>, _, ds, _u => Docs.errors(rest, uri)) == ds : List<&2, Rep.Diag>}
  {==}

# and its text
law pub.get_head:
  for +uri: String
  for -text: String
  for -ds: List<&2, Rep.Diag>
  for -rest: List<&2, Docs.Doc>
  {Docs.get(Docs.Doc{uri, text, ds} <> rest, uri) == Some{text} : Maybe<&2, String>}

def pub.get_head(uri, text, _ds, rest):
  e = Equal.sym(Bool, String.eq(uri, uri), True{}, pub.seq_refl(uri))
  %e : {Lazy.stop(Maybe<&2, String>, _, Some{text}, _u => Docs.get(rest, uri)) == Some{text} : Maybe<&2, String>}
  {==}

# one document onto the rest, the URI's removed: none of its errors survive
law pub.del.step:
  for bb: Bool
  for +u: String
  for +uri: String
  for -t: String
  for -e: List<&2, Rep.Diag>
  for +rest: List<&2, Docs.Doc>
  for h: {String.eq(u, uri) == bb : Bool}
  for ih: {Docs.errors(rest, uri) == [] : List<&2, Rep.Diag>}
  {Docs.errors(Bool.pick(List<&2, Docs.Doc>, bb, rest, Docs.Doc{u, t, e} <> rest), uri) == [] : List<&2, Rep.Diag>}

def pub.del.step(bb, u, uri, _t, e, rest, h, ih):
  match bb:
    case True{}:
      ih
    case False{}:
      g = Equal.sym(Bool, String.eq(u, uri), False{}, h)
      %g : {Lazy.stop(List<&2, Rep.Diag>, _, e, _u => Docs.errors(rest, uri)) == [] : List<&2, Rep.Diag>}
      ih

# the documents without a URI hold no errors for it
law pub.del:
  for docs: List<&2, Docs.Doc>
  for +uri: String
  {Docs.errors(Docs.del(docs, uri), uri) == [] : List<&2, Rep.Diag>}

def pub.del(docs, uri):
  match docs:
    case Nil{}:
      {==}
    case Con{Docs.Doc{+u, t, e}, +r}:
      pub.del.step(String.eq(u, uri), u, uri, t, e, Docs.del(r, uri), {==}, pub.del(r, uri))

def Laws.open_publishes(_uri, _text, _ds, _rs, _docs):
  {==}

def Laws.save_publishes(_uri, _ds, _rs, _docs):
  {==}

def Laws.change_publishes(_uri, _text, _rs, _docs):
  {==}

def Laws.open_keeps(uri, text, ds, _rs, docs):
  (pub.errors_head(uri, Maybe.default(&2, String, Docs.get(Docs.set(docs, uri, text), uri), ""), ds,
      Docs.del(Docs.set(docs, uri, text), uri)),
    Equal.trans(Maybe<&2, String>,
      Docs.get(Docs.set_errors(Docs.set(docs, uri, text), uri, ds), uri),
      Some{Maybe.default(&2, String, Docs.get(Docs.set(docs, uri, text), uri), "")}, Some{text},
      pub.get_head(uri, Maybe.default(&2, String, Docs.get(Docs.set(docs, uri, text), uri), ""), ds,
        Docs.del(Docs.set(docs, uri, text), uri)),
      Equal.cong(Maybe<&2, String>, Maybe<&2, String>, m => Some{Maybe.default(&2, String, m, "")},
        Docs.get(Docs.set(docs, uri, text), uri), Some{text},
        pub.get_head(uri, text, Docs.errors(docs, uri), Docs.del(docs, uri)))))

def Laws.save_keeps(uri, ds, _rs, docs):
  pub.errors_head(uri, Maybe.default(&2, String, Docs.get(docs, uri), ""), ds, Docs.del(docs, uri))

def Laws.change_keeps(uri, text, _rs, docs):
  (pub.errors_head(uri, text, Docs.errors(docs, uri), Docs.del(docs, uri)),
    pub.get_head(uri, text, Docs.errors(docs, uri), Docs.del(docs, uri)))

def Laws.close_publishes(uri, docs):
  ({==}, pub.del(docs, uri))

def Laws.config_unlinted(path, h, _text, _rs):
  e = Equal.sym(Bool, Plan.is_config(path), True{}, h)
  %e : {Bool.pick(List<&2, F.Graded>, _, [], Rules.graded(Config.nearest(_rs), Rules.all(path, _text)))
    == [] : List<&2, F.Graded>}
  {==}

# appending nothing leaves a list as it was
law pub.app_nil:
  for -A: Kind(&2)
  for xs: List<&2, A>
  {List.append(&2, A, xs, []) == xs : List<&2, A>}

def pub.app_nil(A, xs):
  match xs:
    case Nil{}:
      {==}
    case Con{hd, +tl}:
      Equal.cong(List<&2, A>, List<&2, A>, rr => hd <> rr, List.append(&2, A, tl, []), tl, pub.app_nil(A, tl))

# one finding graded alone and put before the rest graded is the rest graded
# with it
law pub.grade.step:
  for bb: Bool
  for -g: F.Graded
  for -a: List<&2, F.Graded>
  for -b: List<&2, F.Graded>
  for e: {a == b : List<&2, F.Graded>}
  {List.append(&2, F.Graded, Bool.pick(List<&2, F.Graded>, bb, [], [g]), a)
    == Bool.pick(List<&2, F.Graded>, bb, b, g <> b) : List<&2, F.Graded>}

def pub.grade.step(bb, g, a, _b, e):
  match bb:
    case True{}:
      e
    case False{}:
      %e : {g <> a == g <> _ : List<&2, F.Graded>}
      {==}

# findings all at one path: the CLI's grading, finding by finding, is
# grading them all by that path's config
law pub.grade_at:
  for +cs: List<&2, Plan.Conf>
  for +world: W.World
  for +path: String
  for fs: List<&2, F.Finding>
  {Plan.grade(cs, world, Rules.on.at(path, fs)) == Rules.graded(Plan.config.at(cs, world, path), Rules.on.at(path, fs))
    : List<&2, F.Graded>}

def pub.grade_at(cs, world, path, fs):
  match fs:
    case Nil{}:
      {==}
    case Con{F.Finding{_p, line, col, len, +rule, msg}, +rest}:
      pub.grade.step(Config.is_off(Config.level(Plan.config.at(cs, world, path), Rules.group(rule), rule)),
        F.Graded{Config.level(Plan.config.at(cs, world, path), Rules.group(rule), rule),
          F.Finding{path, line, col, len, rule, msg}},
        Plan.grade(cs, world, Rules.on.at(path, rest)),
        Rules.graded(Plan.config.at(cs, world, path), Rules.on.at(path, rest)),
        pub.grade_at(cs, world, path, rest))

# a table whose first row is a directory's own: its config is that row's
law pub.find_head:
  for +d: String
  for -rest: List<&2, Plan.Conf>
  for +world: W.World
  {Plan.conf.find(Plan.Conf{d, Plan.conf.near(world, d)} <> rest, world, d) == Plan.conf.near(world, d)
    : Config.Config}

def pub.find_head(d, rest, world):
  e = Equal.sym(Bool, String.eq(d, d), True{}, pub.seq_refl(d))
  %e : {Lazy.stop(Config.Config, _, Plan.conf.near(world, d), _u => Plan.conf.find(rest, world, d))
    == Plan.conf.near(world, d) : Config.Config}
  {==}

# `bolt <path>` runs over that path alone, unless it is a bolt.bend
law pub.cli.named:
  for +world: W.World
  for +path: String
  for h: {W.paths.of(world) == [path] : List<&2, String>}
  {Plan.inputs(world) == Plan.sources([path]) : List<&2, String>}

def pub.cli.named(world, path, h):
  e = Equal.sym(List<&2, String>, W.paths.of(world), [path], h)
  %e : {Plan.sources(Plan.files.named(_, world)) == Plan.sources([path]) : List<&2, String>}
  {==}

# the LSP's lint and the CLI's per-file findings for a source (bb False) or
# a bolt.bend (bb True)
law pub.cli.case:
  for bb: Bool
  for +world: W.World
  for +path: String
  for +text: String
  for hc: {Plan.is_config(path) == bb : Bool}
  for ht: {W.text(world, path) == Some{text} : Maybe<&2, String>}
  {Server.pub.lint(path, text, Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world))
    == Plan.grade(Plan.confs.at(Plan.conf.dirs(Bool.pick(List<&2, String>, bb, [], [path])), world), world,
      Plan.per_file(Plan.srcs_of(Plan.gots(Bool.pick(List<&2, String>, bb, [], [path]), world))))
    : List<&2, F.Graded>}

def pub.cli.case(bb, world, path, text, hc, ht):
  match bb:
    case True{}:
      e = Equal.sym(Bool, Plan.is_config(path), True{}, hc)
      %e : {Bool.pick(List<&2, F.Graded>, _, [],
          Rules.graded(Config.nearest(Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)),
            Rules.all(path, text)))
        == [] : List<&2, F.Graded>}
      {==}
    case False{}:
      e = Equal.sym(Bool, Plan.is_config(path), False{}, hc)
      %e : {Bool.pick(List<&2, F.Graded>, _, [],
          Rules.graded(Config.nearest(Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)),
            Rules.all(path, text)))
        == Plan.grade(Plan.confs.at(Plan.conf.dirs([path]), world), world,
          Plan.per_file(Plan.srcs_of(Plan.gots([path], world))))
        : List<&2, F.Graded>}
      t = Equal.sym(Maybe<&2, String>, W.text(world, path), Some{text}, ht)
      %t : {Rules.graded(Config.nearest(Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)),
          Rules.all(path, text))
        == Plan.grade(Plan.confs.at(Plan.conf.dirs([path]), world), world,
          Plan.per_file(Plan.srcs_of([Plan.Got{path, _}])))
        : List<&2, F.Graded>}
      a = Equal.sym(List<&2, F.Finding>, List.append(&2, F.Finding, Rules.all(path, text), []), Rules.all(path, text),
        pub.app_nil(F.Finding, Rules.all(path, text)))
      %a : {Rules.graded(Config.nearest(Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)),
          Rules.all(path, text))
        == Plan.grade(Plan.confs.at(Plan.conf.dirs([path]), world), world, _)
        : List<&2, F.Graded>}
      Equal.sym(List<&2, F.Graded>,
        Plan.grade(Plan.confs.at(Plan.conf.dirs([path]), world), world, Rules.all(path, text)),
        Rules.graded(Config.nearest(Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)),
          Rules.all(path, text)),
        Equal.trans(List<&2, F.Graded>,
          Plan.grade(Plan.confs.at(Plan.conf.dirs([path]), world), world, Rules.all(path, text)),
          Rules.graded(Plan.config.at(Plan.confs.at(Plan.conf.dirs([path]), world), world, path),
            Rules.all(path, text)),
          Rules.graded(Config.nearest(Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world)),
            Rules.all(path, text)),
          pub.grade_at(Plan.confs.at(Plan.conf.dirs([path]), world), world, path, Rules.on.rules(Src.of(path, text))),
          Equal.cong(Config.Config, List<&2, F.Graded>, c => Rules.graded(c, Rules.all(path, text)),
            Plan.config.at(Plan.confs.at(Plan.conf.dirs([path]), world), world, path),
            Plan.conf.near(world, Config.dir_of(path)),
            pub.find_head(Config.dir_of(path),
              Plan.confs.at(Plan.uniq([Config.dir_of("SPEC.md")], [Config.dir_of(path)]), world), world))))

def Laws.lint_is_cli(world, path, text, h, ht):
  n = Equal.sym(List<&2, String>, Plan.inputs(world), Plan.sources([path]), pub.cli.named(world, path, h))
  %n : {Server.pub.lint(path, text, Plan.texts.at(Server.pub.cands(W.cwd.of(world), path), world))
    == Plan.grade(Plan.confs.at(Plan.conf.dirs(_), world), world, Plan.per_file(Plan.srcs_of(Plan.gots(_, world))))
    : List<&2, F.Graded>}
  pub.cli.case(Plan.is_config(path), world, path, text, {==}, ht)
