# bolt/lsp: the proofs. `bend PROOF.bend` is the gate.
import Base
import 0xa3c2445eb44c5d8406e6229be518fccb/value.bend as J
import ./frame.bend as Frame
import ./server.bend as Server
import ./LAWS.bend as Laws
import ./checker/argv.bend as Argv
import ../paths.bend as Paths
import ./nav.bend as Nav
import ./docs.bend as Docs
import ./proto.bend as Proto
import ./files/service.bend as F
import ../../syntax/bind.bend as Bind
import ../../syntax/outline.bend as Outline
import ../../syntax/word.bend as Word

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

def Laws.unknown_refused(name, h, id, w):
  Equal.trans(List<&2, Server.Reply>, Laws.sent(Server.step(Server.method(name), id, w)),
    Laws.sent(Server.step(Server.MOther{}, id, w)), Laws.refusal(id),
    Equal.cong(Server.Method, List<&2, Server.Reply>, m => Laws.sent(Server.step(m, id, w)), Server.method(name),
      Server.MOther{}, h),
    unknown_other(w, id))

# the checker
# -----------

def Laws.check_only(_path):
  {==}

# a run's flag, or the check-only flag when there is no run
def nav.flag_or(mm: Maybe<&2, Argv.Run>) -> String:
  match mm:
    case None{}:
      "--check-only"
    case Some{rr}:
      Argv.flag(rr)

# whichever way the followup's condition goes, a run it gives checks only
law nav.picked_check_only:
  for cc: Bool
  for +path: String
  for rr: Argv.Run
  for h: {Bool.pick(Maybe<&2, Argv.Run>, cc, Some{Argv.run_of(path)}, None{}) == Some{rr} : Maybe<&2, Argv.Run>}
  {Argv.flag(rr) == "--check-only" : String}

def nav.picked_check_only(cc, path, rr, h):
  match cc:
    case False{}:
      Equal.sym(String, "--check-only", Argv.flag(rr),
        Equal.cong(Maybe<&2, Argv.Run>, String, nav.flag_or, None{}, Some{rr}, h))
    case True{}:
      Equal.sym(String, "--check-only", Argv.flag(rr),
        Equal.cong(Maybe<&2, Argv.Run>, String, nav.flag_or, Some{Argv.run_of(path)}, Some{rr}, h))

def Laws.followup_check_only(ds, path, rr, h):
  nav.picked_check_only(Bool.and(Argv.only_todos(ds), Paths.is_laws(path)), Argv.proof_path(path), rr, h)

# navigation
# ----------

# Unit for no text, Empty for one
def nav.none_ty(mm: Maybe<&2, String>) -> Type:
  match mm:
    case None{}:
      Unit
    case Some{_t}:
      Empty

# no text is some text
law nav.none_some:
  for -t: String
  for e: {None{} == Some{t} : Maybe<&2, String>}
  Empty

def nav.none_some(_t, e):
  %e : nav.none_ty(_)
  Unit{}

# a document the store holds is read from the store, not the files
law nav.miss_open:
  for fs: F.Files
  for mm: Maybe<&2, String>
  for +text: String
  for h: {mm == Some{text} : Maybe<&2, String>}
  for path: String
  for -R: Type
  for k: String -> IO.OP<R>
  {Nav.load.miss(~fs, mm, path, R, k) == k(text) : IO.OP<R>}

def nav.miss_open(fs, mm, text, h, path, R, k):
  match mm:
    case None{}:
      Empty.absurd({Nav.load.miss(~fs, None{}, path, R, k) == k(text) : IO.OP<R>}, nav.none_some(text, h))
    case Some{t}:
      Equal.cong(Maybe<&2, String>, IO.OP<R>, m => k(Maybe.default(&2, String, m, "")), Some{t}, Some{text}, h)

def Laws.nav_open_text(fs, docs, uri, text, h, R, k):
  nav.miss_open(fs, Docs.get(docs, uri), text, h, Proto.path(uri), R, k)

# the binder as the server wraps it is the binder as the law wraps it
law nav.here_local:
  for mm: Maybe<&2, Bind.Bind>
  for uri: String
  {Nav.here(mm, uri) == Laws.nav.local(mm, uri) : Maybe<&2, Nav.Found>}

def nav.here_local(mm, _uri):
  match mm:
    case None{}:
      {==}
    case Some{_b}:
      {==}

# at a binder, definition answers that binder
law nav.site_binder:
  for fs: F.Files
  for site: Maybe<&2, Bind.Site>
  for b: Bind.Bind
  for hs: {site == Some{Bind.SBind{b}} : Maybe<&2, Bind.Site>}
  for binds: List<&2, Bind.Bind>
  for docs: List<&2, Docs.Doc>
  for +uri: String
  for name: String
  for -R: Type
  for k: Maybe<&2, Nav.Found> -> IO.OP<R>
  {Nav.at.site(~fs, site, binds, docs, uri, name, R, k) == k(Some{Nav.Here{uri, b}}) : IO.OP<R>}

def nav.site_binder(fs, site, b, hs, binds, docs, uri, name, R, k):
  hs2 = Equal.sym(Maybe<&2, Bind.Site>, site, Some{Bind.SBind{b}}, hs)
  %hs2 : {Nav.at.site(~fs, _, binds, docs, uri, name, R, k) == k(Some{Nav.Here{uri, b}}) : IO.OP<R>}
  {==}

# at a use of a binder of the document, definition answers that binder
law nav.site_local:
  for fs: F.Files
  for site: Maybe<&2, Bind.Site>
  for n: String
  for l: U32
  for c: U32
  for +tl: U32
  for +tc: U32
  for hs: {site == Some{Bind.SUse{Bind.Use{n, l, c, Bind.TLocal{tl, tc}}}} : Maybe<&2, Bind.Site>}
  for +binds: List<&2, Bind.Bind>
  for docs: List<&2, Docs.Doc>
  for +uri: String
  for name: String
  for -R: Type
  for k: Maybe<&2, Nav.Found> -> IO.OP<R>
  {Nav.at.site(~fs, site, binds, docs, uri, name, R, k) == k(Laws.nav.local(Bind.binder(binds, tl, tc), uri))
    : IO.OP<R>}

def nav.site_local(fs, site, n, l, c, tl, tc, hs, binds, docs, uri, name, R, k):
  hs2 = Equal.sym(Maybe<&2, Bind.Site>, site, Some{Bind.SUse{Bind.Use{n, l, c, Bind.TLocal{tl, tc}}}}, hs)
  %hs2 : {Nav.at.site(~fs, _, binds, docs, uri, name, R, k) == k(Laws.nav.local(Bind.binder(binds, tl, tc), uri))
    : IO.OP<R>}
  Equal.cong(Maybe<&2, Nav.Found>, IO.OP<R>, k, Nav.here(Bind.binder(binds, tl, tc), uri),
    Laws.nav.local(Bind.binder(binds, tl, tc), uri), nav.here_local(Bind.binder(binds, tl, tc), uri))

# definition over a parsed document, at a binder
law nav.bound_binder:
  for fs: F.Files
  for bb: Bind.Bound
  for docs: List<&2, Docs.Doc>
  for +uri: String
  for name: String
  for +line: U32
  for +col: U32
  for b: Bind.Bind
  for hs: {Bind.at(bb, line, col) == Some{Bind.SBind{b}} : Maybe<&2, Bind.Site>}
  for -R: Type
  for k: Maybe<&2, Nav.Found> -> IO.OP<R>
  {Nav.at.bound(~fs, bb, docs, uri, name, line, col, R, k) == k(Some{Nav.Here{uri, b}}) : IO.OP<R>}

def nav.bound_binder(fs, bb, docs, uri, name, line, col, b, hs, R, k):
  match bb:
    case Bind.Bound{+binds, uses, scopes}:
      nav.site_binder(fs, Bind.at(Bind.Bound{binds, uses, scopes}, line, col), b, hs, binds, docs, uri, name, R, k)

# definition over a parsed document, at a use of one of its binders
law nav.bound_local:
  for fs: F.Files
  for bb: Bind.Bound
  for docs: List<&2, Docs.Doc>
  for +uri: String
  for name: String
  for +line: U32
  for +col: U32
  for n: String
  for l: U32
  for c: U32
  for +tl: U32
  for +tc: U32
  for hs: {Bind.at(bb, line, col) == Some{Bind.SUse{Bind.Use{n, l, c, Bind.TLocal{tl, tc}}}} : Maybe<&2, Bind.Site>}
  for -R: Type
  for k: Maybe<&2, Nav.Found> -> IO.OP<R>
  {Nav.at.bound(~fs, bb, docs, uri, name, line, col, R, k)
    == k(Laws.nav.local(Bind.binder(Laws.nav.binds(bb), tl, tc), uri)) : IO.OP<R>}

def nav.bound_local(fs, bb, docs, uri, name, line, col, n, l, c, tl, tc, hs, R, k):
  match bb:
    case Bind.Bound{+binds, uses, scopes}:
      nav.site_local(fs, Bind.at(Bind.Bound{binds, uses, scopes}, line, col), n, l, c, tl, tc, hs, binds, docs, uri,
        name, R, k)

# hover over a parsed document, at a use of one of its binders
law nav.hover_bound_local:
  for fs: F.Files
  for bb: Bind.Bound
  for items: List<&2, Outline.Item>
  for docs: List<&2, Docs.Doc>
  for +uri: String
  for name: String
  for +line: U32
  for +col: U32
  for n: String
  for l: U32
  for c: U32
  for +tl: U32
  for +tc: U32
  for hs: {Bind.at(bb, line, col) == Some{Bind.SUse{Bind.Use{n, l, c, Bind.TLocal{tl, tc}}}} : Maybe<&2, Bind.Site>}
  for -R: Type
  for k: Maybe<&2, Nav.Found> -> IO.OP<R>
  {Nav.hover.bound(~fs, bb, items, docs, uri, name, line, col, R, k)
    == k(Laws.nav.local(Bind.binder(Laws.nav.binds(bb), tl, tc), uri)) : IO.OP<R>}

def nav.hover_bound_local(fs, bb, items, docs, uri, name, line, col, n, l, c, tl, tc, hs, R, k):
  match bb:
    case Bind.Bound{+binds, uses, scopes}:
      hs2 = Equal.sym(Maybe<&2, Bind.Site>, Bind.at(Bind.Bound{binds, uses, scopes}, line, col),
        Some{Bind.SUse{Bind.Use{n, l, c, Bind.TLocal{tl, tc}}}}, hs)
      %hs2 : {Nav.hover.site(~fs, _, items, binds, docs, uri, name, R, k)
        == k(Laws.nav.local(Bind.binder(binds, tl, tc), uri)) : IO.OP<R>}
      Equal.cong(Maybe<&2, Nav.Found>, IO.OP<R>, k, Nav.here(Bind.binder(binds, tl, tc), uri),
        Laws.nav.local(Bind.binder(binds, tl, tc), uri), nav.here_local(Bind.binder(binds, tl, tc), uri))

def Laws.nav_definition_binder(fs, docs, uri, text, h, line, col, b, hs, R, k):
  h2 = Equal.sym(Maybe<&2, String>, Docs.get(docs, uri), Some{text}, h)
  %h2 : {Nav.load.miss(~fs, _, Proto.path(uri), R, tt => Nav.at.in(~fs, tt, docs, uri, line, col, R, k))
    == k(Some{Nav.Here{uri, b}}) : IO.OP<R>}
  nav.bound_binder(fs, Bind.bound(text), docs, uri, Word.at(text, line, col), line, col, b, hs, R, k)

def Laws.nav_definition_local(fs, docs, uri, text, h, line, col, n, l, c, tl, tc, hs, R, k):
  h2 = Equal.sym(Maybe<&2, String>, Docs.get(docs, uri), Some{text}, h)
  %h2 : {Nav.load.miss(~fs, _, Proto.path(uri), R, tt => Nav.at.in(~fs, tt, docs, uri, line, col, R, k))
    == k(Laws.nav.local(Bind.binder(Laws.nav.binds(Bind.bound(text)), tl, tc), uri)) : IO.OP<R>}
  nav.bound_local(fs, Bind.bound(text), docs, uri, Word.at(text, line, col), line, col, n, l, c, tl, tc, hs, R, k)

def Laws.nav_hover_local(fs, docs, uri, text, h, line, col, n, l, c, tl, tc, hs, R, k):
  h2 = Equal.sym(Maybe<&2, String>, Docs.get(docs, uri), Some{text}, h)
  %h2 : {Nav.load.miss(~fs, _, Proto.path(uri), R, tt => Nav.hover.in(~fs, tt, docs, uri, line, col, R, k))
    == k(Laws.nav.local(Bind.binder(Laws.nav.binds(Bind.bound(text)), tl, tc), uri)) : IO.OP<R>}
  nav.hover_bound_local(fs, Bind.bound(text), Outline.items(text), docs, uri, Word.at(text, line, col), line, col,
    n, l, c, tl, tc, hs, R, k)

# the server's positions for a site are the law's, whatever the site
law nav.sites_spec:
  for site: Maybe<&2, Bind.Site>
  for +bb: Bind.Bound
  {Nav.sites.of(site, bb) == Laws.nav.referenced(site, bb) : Nav.Sites}

def nav.sites_spec(site, _bb):
  match site:
    case None{}:
      {==}
    case Some{ss}:
      match ss:
        case Bind.SBind{b}:
          match b:
            case Bind.Bind{_name, _l, _c, kind, _note}:
              match kind:
                case Bind.KItem{}:
                  {==}
                case Bind.KCtor{}:
                  {==}
                case Bind.KParam{}:
                  {==}
                case Bind.KTypeParam{}:
                  {==}
                case Bind.KField{}:
                  {==}
                case Bind.KLocal{}:
                  {==}
                case Bind.KPat{}:
                  {==}
                case Bind.KFor{}:
                  {==}
                case Bind.KTypeVar{}:
                  {==}
        case Bind.SUse{u}:
          match u:
            case Bind.Use{_n, _l, _c, tg}:
              match tg:
                case Bind.TLocal{_tl, _tc}:
                  {==}
                case Bind.TItem{_item}:
                  {==}
                case Bind.TQual{_alias, _name}:
                  {==}
                case Bind.TFree{}:
                  {==}

def Laws.nav_references(fs, docs, uri, text, h, line, col, R, k):
  h2 = Equal.sym(Maybe<&2, String>, Docs.get(docs, uri), Some{text}, h)
  %h2 : {Nav.load.miss(~fs, _, Proto.path(uri), R, tt => k(Nav.sites.in(tt, line, col)))
    == k(Laws.nav.referenced(Bind.at(Bind.bound(text), line, col), Bind.bound(text))) : IO.OP<R>}
  Equal.cong(Nav.Sites, IO.OP<R>, k, Nav.sites.in(text, line, col),
    Laws.nav.referenced(Bind.at(Bind.bound(text), line, col), Bind.bound(text)),
    nav.sites_spec(Bind.at(Bind.bound(text), line, col), Bind.bound(text)))

def Laws.nav_completion(fs, docs, uri, text, h, prefix, line, hp, R, k):
  h2 = Equal.sym(Maybe<&2, String>, Docs.get(docs, uri), Some{text}, h)
  hp2 = Equal.sym(Maybe<&2, String>, Outline.import_path(Outline.items(text), Word.head(prefix)), None{}, hp)
  %h2 : {Nav.load.miss(~fs, _, Proto.path(uri), R, tt => Nav.candidates.in(~fs, tt, docs, uri, prefix, line, R, k))
    == Nav.from_base(~fs, Bool.not(String.is_empty(prefix)), docs, prefix, R,
      base => k(List.append(&2, Outline.Item, Laws.nav.locals(text, prefix, line), Laws.nav.after(text, prefix, base))))
    : IO.OP<R>}
  %hp2 : {Nav.candidates.via(~fs, _, Outline.items(text), docs, uri, prefix,
      Nav.as_items(Bind.visible(Bind.bound(text), line)), R, k)
    == Nav.from_base(~fs, Bool.not(String.is_empty(prefix)), docs, prefix, R,
      base => k(List.append(&2, Outline.Item, Laws.nav.locals(text, prefix, line), Laws.nav.after(text, prefix, base))))
    : IO.OP<R>}
  {==}

