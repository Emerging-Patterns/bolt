# proofs of laws/OutlineListsTopLevelItems.bend
import Base
import ../src/syntax/lex.bend as Lex
import ../src/syntax/outline.bend as Outline
import ../src/lazy/lazy.bend as Lazy
import ../laws/OutlineListsTopLevelItems.bend as Laws
import ../laws/defs/LineBreakChar.bend as D1
import ./lemmas/LexAndTreeFacts.bend as M1

# the outline (laws/OutlineListsTopLevelItems.bend)
# ------------------------
# The machine's state is read as the items it has settled, by kind, name and
# line, newest first (a pending header counts), and the line it is on. Each
# line adds the item the spec says it opens, or none, and moves one line on;
# the flags of the lines that start inside a string are the spec's.

# reversing a list with one item picked on or not: that item moves across
law ol.rev_pick:
  for -A: Data
  for +b: Bool
  for +i: A
  for +xs: List<&2, A>
  for +acc: List<&2, A>
  {List.reverse.go(&2, A, Bool.pick(List<&2, A>, b, i <> xs, xs), acc)
    == List.reverse.go(&2, A, xs, Bool.pick(List<&2, A>, b, i <> acc, acc)) : List<&2, A>}

def ol.rev_pick(_A, b, _i, _xs, _acc):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# reversing an append onto acc: the first list reversed onto acc, then the second
law ol.rev_app:
  for -A: Data
  for +xs: List<&2, A>
  for +ys: List<&2, A>
  for +acc: List<&2, A>
  {List.reverse.go(&2, A, List.append(&2, A, xs, ys), acc)
    == List.reverse.go(&2, A, ys, List.reverse.go(&2, A, xs, acc)) : List<&2, A>}

def ol.rev_app(A, xs, ys, acc):
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      ol.rev_app(A, t, ys, h <> acc)

# a list onto nothing is itself
law ol.app_nil:
  for -A: Data
  for +xs: List<&2, A>
  {List.append(&2, A, xs, []) == xs : List<&2, A>}

def ol.app_nil(A, xs):
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.cong(List<&2, A>, List<&2, A>, r => h <> r, List.append(&2, A, t, []), t, ol.app_nil(A, t))

# reversing twice: what was under the first reversal, then the list, then ys
law ol.rev_rev:
  for -A: Data
  for +xs: List<&2, A>
  for +acc: List<&2, A>
  for +ys: List<&2, A>
  {List.reverse.go(&2, A, List.reverse.go(&2, A, xs, acc), ys)
    == List.reverse.go(&2, A, acc, List.append(&2, A, xs, ys)) : List<&2, A>}

def ol.rev_rev(A, xs, acc, ys):
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      ol.rev_rev(A, t, h <> acc, ys)

# the outline's flags of a text's line breaks, pushed onto acc, are the
# spec's, reversed onto acc
law ol.breaks:
  for +tt: String
  for +s: Bool
  for +acc: List<&2, Bool>
  {Outline.breaks(tt, s, acc) == List.reverse.go(&2, Bool, Laws.top.breaks(tt, s), acc) : List<&2, Bool>}

def ol.breaks(tt, s, acc):
  match tt:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      Equal.trans(List<&2, Bool>,
        Outline.breaks(t, s, Bool.pick(List<&2, Bool>, D1.breaks(h), s <> acc, acc)),
        List.reverse.go(&2, Bool, Laws.top.breaks(t, s), Bool.pick(List<&2, Bool>, D1.breaks(h), s <> acc, acc)),
        List.reverse.go(&2, Bool, Laws.top.breaks(SCon{h, t}, s), acc),
        ol.breaks(t, s, Bool.pick(List<&2, Bool>, D1.breaks(h), s <> acc, acc)),
        Equal.sym(List<&2, Bool>,
          List.reverse.go(&2, Bool, Laws.top.breaks(SCon{h, t}, s), acc),
          List.reverse.go(&2, Bool, Laws.top.breaks(t, s), Bool.pick(List<&2, Bool>, D1.breaks(h), s <> acc, acc)),
          ol.rev_pick(Bool, D1.breaks(h), s, Laws.top.breaks(t, s), acc)))

# the outline's flags of the tokens' line breaks, pushed onto acc, are the
# spec's, reversed onto acc
law ol.inside:
  for +toks: List<&2, Lex.Tok>
  for +acc: List<&2, Bool>
  {Outline.inside.go(toks, acc) == List.reverse.go(&2, Bool, Laws.top.strung(toks), acc) : List<&2, Bool>}

def ol.inside(toks, acc):
  match toks:
    case Nil{}:
      {==}
    case Con{Lex.Tok{+k, +t, +l, +c}, +rest}:
      Equal.trans(List<&2, Bool>,
        Outline.inside.go(rest, Outline.breaks(t, Lex.is_str(k), acc)),
        List.reverse.go(&2, Bool, Laws.top.strung(rest), Outline.breaks(t, Lex.is_str(k), acc)),
        List.reverse.go(&2, Bool, Laws.top.strung(Lex.Tok{k, t, l, c} <> rest), acc),
        ol.inside(rest, Outline.breaks(t, Lex.is_str(k), acc)),
        Equal.trans(List<&2, Bool>,
          List.reverse.go(&2, Bool, Laws.top.strung(rest), Outline.breaks(t, Lex.is_str(k), acc)),
          List.reverse.go(&2, Bool, Laws.top.strung(rest),
            List.reverse.go(&2, Bool, Laws.top.breaks(t, Lex.is_str(k)), acc)),
          List.reverse.go(&2, Bool, Laws.top.strung(Lex.Tok{k, t, l, c} <> rest), acc),
          Equal.cong(List<&2, Bool>, List<&2, Bool>, x => List.reverse.go(&2, Bool, Laws.top.strung(rest), x),
            Outline.breaks(t, Lex.is_str(k), acc),
            List.reverse.go(&2, Bool, Laws.top.breaks(t, Lex.is_str(k)), acc),
            ol.breaks(t, Lex.is_str(k), acc)),
          Equal.sym(List<&2, Bool>,
            List.reverse.go(&2, Bool, Laws.top.strung(Lex.Tok{k, t, l, c} <> rest), acc),
            List.reverse.go(&2, Bool, Laws.top.strung(rest),
              List.reverse.go(&2, Bool, Laws.top.breaks(t, Lex.is_str(k)), acc)),
            ol.rev_app(Bool, Laws.top.breaks(t, Lex.is_str(k)), Laws.top.strung(rest), acc))))

# the outline's line flags are the spec's: line 0 outside, then one per break
law ol.flags:
  for +toks: List<&2, Lex.Tok>
  {Outline.inside(toks) == False{} <> Laws.top.strung(toks) : List<&2, Bool>}

def ol.flags(toks):
  Equal.cong(List<&2, Bool>, List<&2, Bool>, x => False{} <> x,
    List.reverse(&2, Bool, Outline.inside.go(toks, [])), Laws.top.strung(toks),
    Equal.trans(List<&2, Bool>,
      List.reverse(&2, Bool, Outline.inside.go(toks, [])),
      List.reverse(&2, Bool, List.reverse.go(&2, Bool, Laws.top.strung(toks), [])),
      Laws.top.strung(toks),
      Equal.cong(List<&2, Bool>, List<&2, Bool>, x => List.reverse(&2, Bool, x),
        Outline.inside.go(toks, []), List.reverse.go(&2, Bool, Laws.top.strung(toks), []),
        ol.inside(toks, [])),
      Equal.trans(List<&2, Bool>,
        List.reverse(&2, Bool, List.reverse.go(&2, Bool, Laws.top.strung(toks), [])),
        List.append(&2, Bool, Laws.top.strung(toks), []),
        Laws.top.strung(toks),
        ol.rev_rev(Bool, Laws.top.strung(toks), [], []),
        ol.app_nil(Bool, Laws.top.strung(toks)))))

# reversing onto a text: the reversal, then the text
law ol.srev:
  for +acc: String
  for +x: String
  {String.reverse.go(acc, x) == String.append(String.reverse.go(acc, SNil{}), x) : String}

def ol.srev(acc, x):
  match acc:
    case SNil{}:
      {==}
    case SCon{+a, +rest}:
      Equal.trans(String,
        String.reverse.go(rest, SCon{a, x}),
        String.append(String.reverse.go(rest, SNil{}), SCon{a, x}),
        String.append(String.reverse.go(SCon{a, rest}, SNil{}), x),
        ol.srev(rest, SCon{a, x}),
        Equal.sym(String,
          String.append(String.reverse.go(SCon{a, rest}, SNil{}), x),
          String.append(String.reverse.go(rest, SNil{}), SCon{a, x}),
          Equal.trans(String,
            String.append(String.reverse.go(rest, SCon{a, SNil{}}), x),
            String.append(String.append(String.reverse.go(rest, SNil{}), SCon{a, SNil{}}), x),
            String.append(String.reverse.go(rest, SNil{}), SCon{a, x}),
            Equal.cong(String, String, y => String.append(y, x),
              String.reverse.go(rest, SCon{a, SNil{}}),
              String.append(String.reverse.go(rest, SNil{}), SCon{a, SNil{}}),
              ol.srev(rest, SCon{a, SNil{}})),
            M1.app.assoc(String.reverse.go(rest, SNil{}), SCon{a, SNil{}}, x))))

# the name's next char, whether or not it stops the name
law ol.name.arm:
  for +b: Bool
  for +t: String
  for +h: Char
  for +acc: String
  for +ih: {Outline.name.go(t, SCon{h, acc}, False{})
    == String.append(String.reverse(SCon{h, acc}), Laws.top.name(t)) : String}
  {Outline.name.go(t, Outline.name.push(b, h, acc), b)
    == String.append(String.reverse(acc), Bool.pick(String, b, SNil{}, SCon{h, Laws.top.name(t)})) : String}

def ol.name.arm(b, t, h, acc, ih):
  match b:
    case True{}:
      match t:
        case SNil{}:
          Equal.sym(String, String.append(String.reverse(acc), SNil{}), String.reverse(acc),
            M1.app.nil(String.reverse(acc)))
        case SCon{_h2, _t2}:
          Equal.sym(String, String.append(String.reverse(acc), SNil{}), String.reverse(acc),
            M1.app.nil(String.reverse(acc)))
    case False{}:
      Equal.trans(String,
        Outline.name.go(t, SCon{h, acc}, False{}),
        String.append(String.reverse(SCon{h, acc}), Laws.top.name(t)),
        String.append(String.reverse(acc), SCon{h, Laws.top.name(t)}),
        ih,
        Equal.trans(String,
          String.append(String.reverse.go(acc, SCon{h, SNil{}}), Laws.top.name(t)),
          String.append(String.append(String.reverse(acc), SCon{h, SNil{}}), Laws.top.name(t)),
          String.append(String.reverse(acc), SCon{h, Laws.top.name(t)}),
          Equal.cong(String, String, y => String.append(y, Laws.top.name(t)),
            String.reverse.go(acc, SCon{h, SNil{}}),
            String.append(String.reverse(acc), SCon{h, SNil{}}),
            ol.srev(acc, SCon{h, SNil{}})),
          M1.app.assoc(String.reverse(acc), SCon{h, SNil{}}, Laws.top.name(t))))

# the name read with acc (reversed) before it: acc, then the spec's name
law ol.name.go:
  for +ss: String
  for +acc: String
  {Outline.name.go(ss, acc, False{}) == String.append(String.reverse(acc), Laws.top.name(ss)) : String}

def ol.name.go(ss, acc):
  match ss:
    case SNil{}:
      Equal.sym(String, String.append(String.reverse(acc), SNil{}), String.reverse(acc),
        M1.app.nil(String.reverse(acc)))
    case SCon{+h, +t}:
      ol.name.arm(Laws.top.stop(h), t, h, acc, ol.name.go(t, SCon{h, acc}))

# the outline's name is the spec's
law ol.name:
  for +ss: String
  {Outline.name(ss) == Laws.top.name(ss) : String}

def ol.name(ss):
  ol.name.go(ss, SNil{})

# words that compare equal, bit by bit past the first: the rest equal, the
# first bits the same
law ol.weq.arm:
  for -p: Nat
  for -at: Word(p)
  for -bt: Word(p)
  for c: Cmp
  for ec: {Word.cmp(p, at, bt) == c : Cmp}
  for ih: {Cmp.is_eq(Word.cmp(p, at, bt)) == True{} : Bool} -> {at == bt : Word(p)}
  for ab: Bool
  for bb: Bool
  for e: {Cmp.is_eq(Word.cmp.fin(ab, bb, c)) == True{} : Bool}
  {WCon{ab, at} == WCon{bb, bt} : Word.Con<p>}

def ol.weq.arm(p, at, bt, c, ec, ih, ab, bb, e):
  match c:
    case LT{}:
      Empty.absurd({WCon{ab, at} == WCon{bb, bt} : Word.Con<p>}, M1.false_true(e))
    case GT{}:
      Empty.absurd({WCon{ab, at} == WCon{bb, bt} : Word.Con<p>}, M1.false_true(e))
    case EQ{}:
      match ab bb:
        case False{} False{}:
          Equal.cong(Word(p), Word.Con<p>, w => WCon{False{}, w}, at, bt,
            ih(Equal.cong(Cmp, Bool, x => Cmp.is_eq(x), Word.cmp(p, at, bt), EQ{}, ec)))
        case True{} True{}:
          Equal.cong(Word(p), Word.Con<p>, w => WCon{True{}, w}, at, bt,
            ih(Equal.cong(Cmp, Bool, x => Cmp.is_eq(x), Word.cmp(p, at, bt), EQ{}, ec)))
        case False{} True{}:
          Empty.absurd({WCon{False{}, at} == WCon{True{}, bt} : Word.Con<p>}, M1.false_true(e))
        case True{} False{}:
          Empty.absurd({WCon{True{}, at} == WCon{False{}, bt} : Word.Con<p>}, M1.false_true(e))

# words that compare equal are equal
law ol.weq:
  for n: Nat
  for a: Word(n)
  for b: Word(n)
  for e: {Cmp.is_eq(Word.cmp(n, a, b)) == True{} : Bool}
  {a == b : Word(n)}

def ol.weq(n, a, b, e):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+(+p):
      match a b:
        case WCon{ab, +at} WCon{bb, +bt}:
          ol.weq.arm(p, at, bt, Word.cmp(p, at, bt), {==}, x => ol.weq(p, at, bt, x), ab, bb, e)

# U32s that compare equal are equal
law ol.ueq:
  for a: U32
  for b: U32
  for e: {U32.is_eq(a, b) == True{} : Bool}
  {a == b : U32}

def ol.ueq(a, b, e):
  match a b:
    case U32{x} U32{y}:
      Equal.cong(Word(32n), U32, w => U32{w}, x, y, ol.weq(32n, x, y, e))

# what a state has settled: its items by kind, name and line, newest first
# (a pending header counts), and the line it is on
type Seen is Data:
  Seen{keys: List<&2, Outline.Item>, line: U32}

# a state as what it has settled
def shown(st: Outline.St) -> Seen:
  match st:
    case Outline.St{mode, n, _doc, out}:
      Seen{Laws.top.keys(Outline.flush(mode, out)), n}

# what a line that opens no item leaves: the same items, one line on
def ol.same(mode: Outline.Mode, out: List<&2, Outline.Item>, nn: U32) -> Seen:
  Seen{Laws.top.keys(Outline.flush(mode, out)), (nn + 1 : U32)}

# a def header's continuation settles the pending def or keeps it pending
law ol.closed:
  for +colon: Bool
  for +nm: String
  for +ll: U32
  for +dd: String
  for +sig: List<&2, String>
  for +text: String
  for +nn: U32
  for +out: List<&2, Outline.Item>
  {shown(Outline.pend_more.closed(colon, nm, ll, dd, sig, text, nn, out))
    == ol.same(Outline.Pending{Outline.IDef{}, nm, ll, dd, sig}, out, nn) : Seen}

def ol.closed(colon, _nm, _ll, _dd, _sig, _text, _nn, _out):
  match colon:
    case True{}:
      {==}
    case False{}:
      {==}

# more of a pending header opens nothing
law ol.pend:
  for +k: Outline.ItemKind
  for +nm: String
  for +ll: U32
  for +dd: String
  for +sig: List<&2, String>
  for +text: String
  for +nn: U32
  for +out: List<&2, Outline.Item>
  {shown(Outline.pend_more(k, nm, ll, dd, sig, text, nn, out))
    == ol.same(Outline.Pending{k, nm, ll, dd, sig}, out, nn) : Seen}

def ol.pend(k, nm, ll, dd, sig, text, nn, out):
  match k:
    case Outline.IDef{}:
      ol.closed(Outline.ends_colon(text), nm, ll, dd, sig, text, nn, out)
    case Outline.IImport{}:
      {==}
    case Outline.ILaw{}:
      {==}
    case Outline.IType{}:
      {==}
    case Outline.ICtor{}:
      {==}
    case Outline.ILocal{}:
      {==}

# a constructor, or none, adds no key
law ol.ctor.stop:
  for +b: Bool
  for +nm: String
  for +nn: U32
  for +s: String
  for +out: List<&2, Outline.Item>
  {Laws.top.keys(Outline.add(Lazy.stop(Maybe<&2, Outline.Item>, b, None{},
      _u => Some{Outline.Item{Outline.ICtor{}, nm, nn, s, "", ""}}), out))
    == Laws.top.keys(out) : List<&2, Outline.Item>}

def ol.ctor.stop(b, _nm, _nn, _s, _out):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# a line of a type block adds no key
law ol.ctor:
  for +text: String
  for +nn: U32
  for +out: List<&2, Outline.Item>
  {Laws.top.keys(Outline.add(Outline.ctor(text, nn), out)) == Laws.top.keys(out) : List<&2, Outline.Item>}

def ol.ctor(text, nn, out):
  ol.ctor.stop(
    Bool.not(Bool.and(Outline.starts_upper(Outline.lstrip(text)), String.contains(Outline.lstrip(text), "{"))),
    Outline.name(Outline.lstrip(text)), nn, Outline.lstrip(text), out)

# an indented line opens nothing
law ol.indent:
  for +mode: Outline.Mode
  for +text: String
  for +nn: U32
  for +out: List<&2, Outline.Item>
  {shown(Outline.indent(mode, text, nn, out)) == ol.same(mode, out, nn) : Seen}

def ol.indent(mode, text, nn, out):
  match mode:
    case Outline.Top{}:
      {==}
    case Outline.InType{}:
      Equal.cong(List<&2, Outline.Item>, Seen, ks => Seen{ks, (nn + 1 : U32)},
        Laws.top.keys(Outline.add(Outline.ctor(text, nn), out)), Laws.top.keys(out), ol.ctor(text, nn, out))
    case Outline.Pending{k, nm, ll, dd, sig}:
      ol.pend(k, nm, ll, dd, sig, text, nn, out)

# a column-0 line that starts nothing opens nothing
law ol.stray:
  for +mode: Outline.Mode
  for +text: String
  for +nn: U32
  for +out: List<&2, Outline.Item>
  {shown(Outline.stray(mode, text, nn, out)) == ol.same(mode, out, nn) : Seen}

def ol.stray(mode, text, nn, out):
  match mode:
    case Outline.Top{}:
      {==}
    case Outline.InType{}:
      {==}
    case Outline.Pending{k, nm, ll, dd, sig}:
      match k:
        case Outline.IDef{}:
          ol.pend(Outline.IDef{}, nm, ll, dd, sig, text, nn, out)
        case Outline.IImport{}:
          {==}
        case Outline.ILaw{}:
          {==}
        case Outline.IType{}:
          {==}
        case Outline.ICtor{}:
          {==}
        case Outline.ILocal{}:
          {==}

# does a class open an item?
def ol.loud(cls: Outline.Cls) -> Bool:
  match cls:
    case Outline.LImport{}:
      True{}
    case Outline.LDef{}:
      True{}
    case Outline.LLaw{}:
      True{}
    case Outline.LType{}:
      True{}
    case other:
      False{}

# what a class the outline steps on leaves
def ol.after(
  cls: Outline.Cls,
  mode: Outline.Mode,
  ss: String,
  nn: U32,
  doc: List<&2, String>,
  out: List<&2, Outline.Item>
) -> Seen:
  shown(Outline.step.go(cls, mode, ss, nn, doc, out))

# a class that opens no item leaves the same items, one line on
law ol.quiet:
  for +cls: Outline.Cls
  for +mode: Outline.Mode
  for +ss: String
  for +nn: U32
  for +doc: List<&2, String>
  for +out: List<&2, Outline.Item>
  for e: {ol.loud(cls) == False{} : Bool}
  {ol.after(cls, mode, ss, nn, doc, out) == ol.same(mode, out, nn) : Seen}

def ol.quiet(cls, mode, ss, nn, doc, out, e):
  match cls:
    case Outline.LBlank{}:
      {==}
    case Outline.LComment{_t}:
      {==}
    case Outline.LIndent{t}:
      ol.indent(mode, t, nn, out)
    case Outline.LOther{}:
      ol.stray(mode, ss, nn, out)
    case Outline.LImport{}:
      Empty.absurd({ol.after(Outline.LImport{}, mode, ss, nn, doc, out) == ol.same(mode, out, nn) : Seen},
        M1.true_false(e))
    case Outline.LDef{}:
      Empty.absurd({ol.after(Outline.LDef{}, mode, ss, nn, doc, out) == ol.same(mode, out, nn) : Seen},
        M1.true_false(e))
    case Outline.LLaw{}:
      Empty.absurd({ol.after(Outline.LLaw{}, mode, ss, nn, doc, out) == ol.same(mode, out, nn) : Seen},
        M1.true_false(e))
    case Outline.LType{}:
      Empty.absurd({ol.after(Outline.LType{}, mode, ss, nn, doc, out) == ol.same(mode, out, nn) : Seen},
        M1.true_false(e))

# the end of a line of whitespace is blank, indented or other
law ol.hit:
  for +indent: Bool
  for +acc: List<&2, Char>
  for +hh: Char
  for +rest: String
  {ol.loud(Outline.classify.white.hit(indent, acc, hh, rest)) == False{} : Bool}

def ol.hit(indent, _acc, _hh, _rest):
  match indent:
    case True{}:
      {==}
    case False{}:
      {==}

# a line that opens with whitespace opens no item
law ol.white:
  for +tt: String
  for +space: Bool
  for +hh: Char
  for +indent: Bool
  for +acc: List<&2, Char>
  {ol.loud(Outline.classify.white(tt, space, hh, indent, acc)) == False{} : Bool}

def ol.white(tt, space, hh, indent, acc):
  match tt space:
    case SNil{} True{}:
      {==}
    case SNil{} False{}:
      ol.hit(indent, acc, hh, SNil{})
    case SCon{+h2, +r} True{}:
      ol.white(r, Char.is_space(h2), h2, indent, hh <> acc)
    case SCon{+h2, +r} False{}:
      ol.hit(indent, acc, hh, SCon{h2, r})

# not `t`: not `type `
law ol.l_ty:
  for +t: String
  for +b: Bool
  for e: {b == False{} : Bool}
  {ol.loud(Outline.classify.ktype(b, t)) == False{} : Bool}

def ol.l_ty(t, b, e):
  match b:
    case True{}:
      Empty.absurd({ol.loud(Outline.classify.ktype(True{}, t)) == False{} : Bool}, M1.true_false(e))
    case False{}:
      {==}

# not `l`: not `law `
law ol.l_law:
  for +x: U32
  for +t: String
  for +b: Bool
  for e: {b == False{} : Bool}
  for e116: {U32.is_eq(x, 116) == False{} : Bool}
  {ol.loud(Outline.classify.klaw(b, x, t)) == False{} : Bool}

def ol.l_law(x, t, b, e, e116):
  match b:
    case True{}:
      Empty.absurd({ol.loud(Outline.classify.klaw(True{}, x, t)) == False{} : Bool}, M1.true_false(e))
    case False{}:
      ol.l_ty(t, U32.is_eq(x, 116), e116)

# not `@`: not `@unsafe def `
law ol.l_at:
  for +x: U32
  for +t: String
  for +b: Bool
  for e: {b == False{} : Bool}
  for e108: {U32.is_eq(x, 108) == False{} : Bool}
  for e116: {U32.is_eq(x, 116) == False{} : Bool}
  {ol.loud(Outline.classify.kat(b, x, t)) == False{} : Bool}

def ol.l_at(x, t, b, e, e108, e116):
  match b:
    case True{}:
      Empty.absurd({ol.loud(Outline.classify.kat(True{}, x, t)) == False{} : Bool}, M1.true_false(e))
    case False{}:
      ol.l_law(x, t, U32.is_eq(x, 108), e108, e116)

# not `d`: not `def `
law ol.l_def:
  for +x: U32
  for +t: String
  for +b: Bool
  for e: {b == False{} : Bool}
  for e64: {U32.is_eq(x, 64) == False{} : Bool}
  for e108: {U32.is_eq(x, 108) == False{} : Bool}
  for e116: {U32.is_eq(x, 116) == False{} : Bool}
  {ol.loud(Outline.classify.kdef(b, x, t)) == False{} : Bool}

def ol.l_def(x, t, b, e, e64, e108, e116):
  match b:
    case True{}:
      Empty.absurd({ol.loud(Outline.classify.kdef(True{}, x, t)) == False{} : Bool}, M1.true_false(e))
    case False{}:
      ol.l_at(x, t, U32.is_eq(x, 64), e64, e108, e116)

# not `i`: not `import `
law ol.l_imp:
  for +x: U32
  for +t: String
  for +b: Bool
  for e: {b == False{} : Bool}
  for e100: {U32.is_eq(x, 100) == False{} : Bool}
  for e64: {U32.is_eq(x, 64) == False{} : Bool}
  for e108: {U32.is_eq(x, 108) == False{} : Bool}
  for e116: {U32.is_eq(x, 116) == False{} : Bool}
  {ol.loud(Outline.classify.kimp(b, x, t)) == False{} : Bool}

def ol.l_imp(x, t, b, e, e100, e64, e108, e116):
  match b:
    case True{}:
      Empty.absurd({ol.loud(Outline.classify.kimp(True{}, x, t)) == False{} : Bool}, M1.true_false(e))
    case False{}:
      ol.l_def(x, t, U32.is_eq(x, 100), e100, e64, e108, e116)

# what the outline makes of a line's pair of class and text
def ol.use(
  pp: Outline.Cls & String,
  mode: Outline.Mode,
  nn: U32,
  doc: List<&2, String>,
  out: List<&2, Outline.Item>
) -> Seen:
  shown(Outline.step.use(pp, mode, nn, doc, out))

# a line that opens with a space opens no item
law ol.gap:
  for +g: Bool
  for +x: U32
  for +t: String
  for +mode: Outline.Mode
  for +nn: U32
  for +doc: List<&2, String>
  for +out: List<&2, Outline.Item>
  {ol.use(Outline.classify.hold.gap(g, x, Chr{x}, t), mode, nn, doc, out) == ol.same(mode, out, nn) : Seen}

def ol.gap(g, x, t, mode, nn, doc, out):
  match g:
    case True{}:
      ol.quiet(Outline.classify.white.enter(t, x), mode, SNil{}, nn, doc, out,
        ol.white(t, True{}, Char.from_u32(x), U32.is_eq(x, 32), []))
    case False{}:
      ol.quiet(Outline.classify.white.enter(t, x), mode, SCon{Chr{x}, t}, nn, doc, out,
        ol.white(t, True{}, Char.from_u32(x), U32.is_eq(x, 32), []))

# a line whose first char is none of `i`, `d`, `@`, `l` and `t` opens no item
law ol.hash:
  for +h: Bool
  for +sp: Bool
  for +x: U32
  for +t: String
  for +mode: Outline.Mode
  for +nn: U32
  for +doc: List<&2, String>
  for +out: List<&2, Outline.Item>
  for e105: {U32.is_eq(x, 105) == False{} : Bool}
  for e100: {U32.is_eq(x, 100) == False{} : Bool}
  for e64: {U32.is_eq(x, 64) == False{} : Bool}
  for e108: {U32.is_eq(x, 108) == False{} : Bool}
  for e116: {U32.is_eq(x, 116) == False{} : Bool}
  {ol.use(Outline.classify.hold.hash(h, sp, x, Chr{x}, t), mode, nn, doc, out) == ol.same(mode, out, nn) : Seen}

def ol.hash(h, sp, x, t, mode, nn, doc, out, e105, e100, e64, e108, e116):
  match h:
    case True{}:
      {==}
    case False{}:
      match sp:
        case True{}:
          ol.gap(U32.is_eq(x, 32), x, t, mode, nn, doc, out)
        case False{}:
          ol.quiet(Outline.classify.keys(x, t), mode, SCon{Chr{x}, t}, nn, doc, out,
            ol.l_imp(x, t, U32.is_eq(x, 105), e105, e100, e64, e108, e116))

# the outline's words are the spec's
law ol.words:
  for +xs: List<&2, String>
  {List.filter(~String, ~Outline.nonempty, xs) == List.filter(~String, ~Laws.top.word, xs) : List<&2, String>}

def ol.words(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Equal.cong(List<&2, String>, List<&2, String>, r => List.filter.put(String, h, r, Laws.top.word(h)),
        List.filter(~String, ~Outline.nonempty, t), List.filter(~String, ~Laws.top.word, t), ol.words(t))

# what a line that opens mm leaves: that item onto the items settled, one
# line on
def ol.adds(mm: Maybe<&2, Outline.Item>, mode: Outline.Mode, out: List<&2, Outline.Item>, nn: U32) -> Seen:
  Seen{Laws.top.put(mm, Laws.top.keys(Outline.flush(mode, out))), (nn + 1 : U32)}

# a keyword line opens its item when the rest of the keyword follows, and
# nothing when it does not
law ol.kw:
  for +b: Bool
  for +cls: Outline.Cls
  for +mode: Outline.Mode
  for +ss: String
  for +nn: U32
  for +doc: List<&2, String>
  for +out: List<&2, Outline.Item>
  for +mm: Maybe<&2, Outline.Item>
  for on: {ol.after(cls, mode, ss, nn, doc, out) == ol.adds(mm, mode, out, nn) : Seen}
  {ol.after(Outline.classify.kw(b, cls), mode, ss, nn, doc, out)
    == ol.adds(Bool.pick(Maybe<&2, Outline.Item>, b, mm, None{}), mode, out, nn) : Seen}

def ol.kw(b, _cls, mode, ss, nn, _doc, out, _mm, on):
  match b:
    case True{}:
      on
    case False{}:
      ol.stray(mode, ss, nn, out)

# an import line's item, by its words, is the spec's
law ol.import.of:
  for +ws: List<&2, String>
  for +ss: String
  for +nn: U32
  for +dd: String
  for +xs: List<&2, Outline.Item>
  {Laws.top.keys(Outline.add(Outline.import_item.of(ws, ss, nn, dd), xs))
    == Laws.top.put(Laws.top.import(ws, nn), Laws.top.keys(xs)) : List<&2, Outline.Item>}

def ol.import.of(ws, _ss, _nn, _dd, _xs):
  match ws:
    case Nil{}:
      {==}
    case Con{_i, r1}:
      match r1:
        case Nil{}:
          {==}
        case Con{_p, r2}:
          match r2:
            case Nil{}:
              {==}
            case Con{_a, r3}:
              match r3:
                case Nil{}:
                  {==}
                case Con{_al, _r}:
                  {==}

# an import line opens the spec's import
law ol.imp_on:
  for +mode: Outline.Mode
  for +ss: String
  for +nn: U32
  for +doc: List<&2, String>
  for +out: List<&2, Outline.Item>
  {ol.after(Outline.LImport{}, mode, ss, nn, doc, out)
    == ol.adds(Laws.top.import(List.filter(~String, ~Laws.top.word, String.split(ss, ' ')), nn), mode, out, nn) : Seen}

def ol.imp_on(mode, ss, nn, doc, out):
  Equal.trans(Seen,
    Seen{Laws.top.keys(Outline.add(Outline.import_item.of(Outline.words(ss), ss, nn, Outline.doc_text(doc)),
      Outline.flush(mode, out))), (nn + 1 : U32)},
    ol.adds(Laws.top.import(Outline.words(ss), nn), mode, out, nn),
    ol.adds(Laws.top.import(List.filter(~String, ~Laws.top.word, String.split(ss, ' ')), nn), mode, out, nn),
    Equal.cong(List<&2, Outline.Item>, Seen, ks => Seen{ks, (nn + 1 : U32)},
      Laws.top.keys(Outline.add(Outline.import_item.of(Outline.words(ss), ss, nn, Outline.doc_text(doc)),
        Outline.flush(mode, out))),
      Laws.top.put(Laws.top.import(Outline.words(ss), nn), Laws.top.keys(Outline.flush(mode, out))),
      ol.import.of(Outline.words(ss), ss, nn, Outline.doc_text(doc), Outline.flush(mode, out))),
    Equal.cong(List<&2, String>, Seen, ws => ol.adds(Laws.top.import(ws, nn), mode, out, nn),
      Outline.words(ss), List.filter(~String, ~Laws.top.word, String.split(ss, ' ')),
      ol.words(String.split(ss, ' '))))

# a def line settles its def at once, or leaves it pending: either way it is
# listed, by the name the outline reads
law ol.start:
  for +colon: Bool
  for +ss: String
  for +nn: U32
  for +dd: String
  for +xs: List<&2, Outline.Item>
  {shown(Outline.start_def.on(colon, ss, nn, dd, xs))
    == Seen{Outline.Item{Outline.IDef{}, Outline.def_name(ss), nn, "", "", ""} <> Laws.top.keys(xs),
      (nn + 1 : U32)} : Seen}

def ol.start(colon, _ss, _nn, _dd, _xs):
  match colon:
    case True{}:
      {==}
    case False{}:
      {==}

# a def line whose name is read from nm opens the spec's def
law ol.def_on:
  for +mode: Outline.Mode
  for +ss: String
  for +nn: U32
  for +doc: List<&2, String>
  for +out: List<&2, Outline.Item>
  for +nm: String
  for en: {Outline.def_name(ss) == Outline.name(nm) : String}
  {ol.after(Outline.LDef{}, mode, ss, nn, doc, out)
    == ol.adds(Some{Outline.Item{Outline.IDef{}, Laws.top.name(nm), nn, "", "", ""}}, mode, out, nn) : Seen}

def ol.def_on(mode, ss, nn, doc, out, nm, en):
  Equal.trans(Seen,
    shown(Outline.start_def.on(Outline.ends_colon(ss), ss, nn, Outline.doc_text(doc), Outline.flush(mode, out))),
    Seen{Outline.Item{Outline.IDef{}, Outline.def_name(ss), nn, "", "", ""} <> Laws.top.keys(Outline.flush(mode, out)),
      (nn + 1 : U32)},
    ol.adds(Some{Outline.Item{Outline.IDef{}, Laws.top.name(nm), nn, "", "", ""}}, mode, out, nn),
    ol.start(Outline.ends_colon(ss), ss, nn, Outline.doc_text(doc), Outline.flush(mode, out)),
    Equal.cong(String, Seen,
      v => Seen{Outline.Item{Outline.IDef{}, v, nn, "", "", ""} <> Laws.top.keys(Outline.flush(mode, out)),
        (nn + 1 : U32)},
      Outline.def_name(ss), Laws.top.name(nm),
      Equal.trans(String, Outline.def_name(ss), Outline.name(nm), Laws.top.name(nm), en, ol.name(nm))))

# a law line opens the spec's law
law ol.law_on:
  for +mode: Outline.Mode
  for +ss: String
  for +nn: U32
  for +doc: List<&2, String>
  for +out: List<&2, Outline.Item>
  {ol.after(Outline.LLaw{}, mode, ss, nn, doc, out)
    == ol.adds(Some{Outline.Item{Outline.ILaw{}, Laws.top.name(String.drop(ss, 4n)), nn, "", "", ""}},
      mode, out, nn) : Seen}

def ol.law_on(mode, ss, nn, _doc, out):
  Equal.cong(String, Seen,
    v => Seen{Outline.Item{Outline.ILaw{}, v, nn, "", "", ""} <> Laws.top.keys(Outline.flush(mode, out)),
      (nn + 1 : U32)},
    Outline.name(String.drop(ss, 4n)), Laws.top.name(String.drop(ss, 4n)), ol.name(String.drop(ss, 4n)))

# a type line opens the spec's type
law ol.type_on:
  for +mode: Outline.Mode
  for +ss: String
  for +nn: U32
  for +doc: List<&2, String>
  for +out: List<&2, Outline.Item>
  {ol.after(Outline.LType{}, mode, ss, nn, doc, out)
    == ol.adds(Some{Outline.Item{Outline.IType{}, Laws.top.name(String.drop(ss, 5n)), nn, "", "", ""}},
      mode, out, nn) : Seen}

def ol.type_on(mode, ss, nn, _doc, out):
  Equal.cong(String, Seen,
    v => Seen{Outline.Item{Outline.IType{}, v, nn, "", "", ""} <> Laws.top.keys(Outline.flush(mode, out)),
      (nn + 1 : U32)},
    Outline.name(String.drop(ss, 5n)), Laws.top.name(String.drop(ss, 5n)), ol.name(String.drop(ss, 5n)))

# five keyword tests that all fail pick nothing
law ol.none5:
  for +b1: Bool
  for +b2: Bool
  for +b3: Bool
  for +b4: Bool
  for +b5: Bool
  for +a1: Maybe<&2, Outline.Item>
  for +a2: Maybe<&2, Outline.Item>
  for +a3: Maybe<&2, Outline.Item>
  for +a4: Maybe<&2, Outline.Item>
  for +a5: Maybe<&2, Outline.Item>
  for +e1: {b1 == False{} : Bool}
  for +e2: {b2 == False{} : Bool}
  for +e3: {b3 == False{} : Bool}
  for +e4: {b4 == False{} : Bool}
  for +e5: {b5 == False{} : Bool}
  {Bool.pick(Maybe<&2, Outline.Item>, b1, a1, Bool.pick(Maybe<&2, Outline.Item>, b2, a2,
    Bool.pick(Maybe<&2, Outline.Item>, b3, a3, Bool.pick(Maybe<&2, Outline.Item>, b4, a4,
      Bool.pick(Maybe<&2, Outline.Item>, b5, a5, None{}))))) == None{} : Maybe<&2, Outline.Item>}

def ol.none5(b1, b2, b3, b4, b5, a1, a2, a3, a4, a5, e1, e2, e3, e4, e5):
  match b1:
    case True{}:
      Empty.absurd({Bool.pick(Maybe<&2, Outline.Item>, True{}, a1, Bool.pick(Maybe<&2, Outline.Item>, b2, a2,
        Bool.pick(Maybe<&2, Outline.Item>, b3, a3, Bool.pick(Maybe<&2, Outline.Item>, b4, a4,
          Bool.pick(Maybe<&2, Outline.Item>, b5, a5, None{}))))) == None{} : Maybe<&2, Outline.Item>},
        M1.true_false(e1))
    case False{}:
      match b2:
        case True{}:
          Empty.absurd({Bool.pick(Maybe<&2, Outline.Item>, True{}, a2,
            Bool.pick(Maybe<&2, Outline.Item>, b3, a3, Bool.pick(Maybe<&2, Outline.Item>, b4, a4,
              Bool.pick(Maybe<&2, Outline.Item>, b5, a5, None{})))) == None{} : Maybe<&2, Outline.Item>},
            M1.true_false(e2))
        case False{}:
          match b3:
            case True{}:
              Empty.absurd({Bool.pick(Maybe<&2, Outline.Item>, True{}, a3, Bool.pick(Maybe<&2, Outline.Item>, b4, a4,
                Bool.pick(Maybe<&2, Outline.Item>, b5, a5, None{}))) == None{} : Maybe<&2, Outline.Item>},
                M1.true_false(e3))
            case False{}:
              match b4:
                case True{}:
                  Empty.absurd({Bool.pick(Maybe<&2, Outline.Item>, True{}, a4,
                    Bool.pick(Maybe<&2, Outline.Item>, b5, a5, None{})) == None{} : Maybe<&2, Outline.Item>},
                    M1.true_false(e4))
                case False{}:
                  match b5:
                    case True{}:
                      Empty.absurd({Bool.pick(Maybe<&2, Outline.Item>, True{}, a5, None{})
                        == None{} : Maybe<&2, Outline.Item>}, M1.true_false(e5))
                    case False{}:
                      {==}

# a line whose first char is none of `i`, `d`, `@`, `l` and `t` opens no
# item in the spec
law ol.head_none:
  for +x: U32
  for +t: String
  for +nn: U32
  for +e105: {U32.is_eq(x, 105) == False{} : Bool}
  for +e100: {U32.is_eq(x, 100) == False{} : Bool}
  for +e64: {U32.is_eq(x, 64) == False{} : Bool}
  for +e108: {U32.is_eq(x, 108) == False{} : Bool}
  for +e116: {U32.is_eq(x, 116) == False{} : Bool}
  {Laws.top.head(SCon{Chr{x}, t}, nn) == None{} : Maybe<&2, Outline.Item>}

def ol.head_none(x, t, nn, e105, e100, e64, e108, e116):
  ol.none5(String.starts_with(SCon{Chr{x}, t}, "import "), String.starts_with(SCon{Chr{x}, t}, "def "),
    String.starts_with(SCon{Chr{x}, t}, "@unsafe def "), String.starts_with(SCon{Chr{x}, t}, "law "),
    String.starts_with(SCon{Chr{x}, t}, "type "),
    Laws.top.import(List.filter(~String, ~Laws.top.word, String.split(SCon{Chr{x}, t}, ' ')), nn),
    Some{Outline.Item{Outline.IDef{}, Laws.top.name(String.drop(SCon{Chr{x}, t}, 4n)), nn, "", "", ""}},
    Some{Outline.Item{Outline.IDef{}, Laws.top.name(String.drop(SCon{Chr{x}, t}, 12n)), nn, "", "", ""}},
    Some{Outline.Item{Outline.ILaw{}, Laws.top.name(String.drop(SCon{Chr{x}, t}, 4n)), nn, "", "", ""}},
    Some{Outline.Item{Outline.IType{}, Laws.top.name(String.drop(SCon{Chr{x}, t}, 5n)), nn, "", "", ""}},
    Equal.cong(Bool, Bool, b => String.starts_with.go.if("mport ", t, b), U32.is_eq(x, 105), False{}, e105),
    Equal.cong(Bool, Bool, b => String.starts_with.go.if("ef ", t, b), U32.is_eq(x, 100), False{}, e100),
    Equal.cong(Bool, Bool, b => String.starts_with.go.if("unsafe def ", t, b), U32.is_eq(x, 64), False{}, e64),
    Equal.cong(Bool, Bool, b => String.starts_with.go.if("aw ", t, b), U32.is_eq(x, 108), False{}, e108),
    Equal.cong(Bool, Bool, b => String.starts_with.go.if("ype ", t, b), U32.is_eq(x, 116), False{}, e116))

# what a line of code with first char x leaves: what the spec says it opens,
# onto the items settled, one line on
def ol.goal(x: U32, t: String, mode: Outline.Mode, nn: U32, doc: List<&2, String>, out: List<&2, Outline.Item>) -> Type:
  {shown(Outline.step(False{}, SCon{Chr{x}, t}, Outline.St{mode, nn, doc, out}))
    == ol.adds(Bool.pick(Maybe<&2, Outline.Item>, False{}, None{}, Laws.top.head(SCon{Chr{x}, t}, nn)),
      mode, out, nn) : Seen}

# a line that opens with none of the keywords' first chars opens nothing, in
# the outline and in the spec
law ol.plain:
  for +x: U32
  for +t: String
  for +mode: Outline.Mode
  for +nn: U32
  for +doc: List<&2, String>
  for +out: List<&2, Outline.Item>
  for +e105: {U32.is_eq(x, 105) == False{} : Bool}
  for +e100: {U32.is_eq(x, 100) == False{} : Bool}
  for +e64: {U32.is_eq(x, 64) == False{} : Bool}
  for +e108: {U32.is_eq(x, 108) == False{} : Bool}
  for +e116: {U32.is_eq(x, 116) == False{} : Bool}
  ol.goal(x, t, mode, nn, doc, out)

def ol.plain(x, t, mode, nn, doc, out, e105, e100, e64, e108, e116):
  Equal.trans(Seen,
    shown(Outline.step(False{}, SCon{Chr{x}, t}, Outline.St{mode, nn, doc, out})),
    ol.same(mode, out, nn),
    ol.adds(Bool.pick(Maybe<&2, Outline.Item>, False{}, None{}, Laws.top.head(SCon{Chr{x}, t}, nn)), mode, out, nn),
    ol.hash(U32.is_eq(x, 35), Char.is_space(Chr{x}), x, t, mode, nn, doc, out, e105, e100, e64, e108, e116),
    Equal.cong(Maybe<&2, Outline.Item>, Seen, m => ol.adds(m, mode, out, nn),
      None{}, Laws.top.head(SCon{Chr{x}, t}, nn),
      Equal.sym(Maybe<&2, Outline.Item>, Laws.top.head(SCon{Chr{x}, t}, nn), None{},
        ol.head_none(x, t, nn, e105, e100, e64, e108, e116))))

# first char `t`, or none of the keywords'
law ol.c_ty:
  for +x: U32
  for +t: String
  for +mode: Outline.Mode
  for +nn: U32
  for +doc: List<&2, String>
  for +out: List<&2, Outline.Item>
  for +e105: {U32.is_eq(x, 105) == False{} : Bool}
  for +e100: {U32.is_eq(x, 100) == False{} : Bool}
  for +e64: {U32.is_eq(x, 64) == False{} : Bool}
  for +e108: {U32.is_eq(x, 108) == False{} : Bool}
  for +b: Bool
  for +e: {U32.is_eq(x, 116) == b : Bool}
  ol.goal(x, t, mode, nn, doc, out)

def ol.c_ty(x, t, mode, nn, doc, out, e105, e100, e64, e108, b, e):
  match b:
    case True{}:
      %Equal.sym(U32, x, 116, ol.ueq(x, 116, e)) : ol.goal(_, t, mode, nn, doc, out)
      ol.kw(String.starts_with(t, "ype "), Outline.LType{}, mode, SCon{Chr{116}, t}, nn, doc, out,
        Some{Outline.Item{Outline.IType{}, Laws.top.name(String.drop(SCon{Chr{116}, t}, 5n)), nn, "", "", ""}},
        ol.type_on(mode, SCon{Chr{116}, t}, nn, doc, out))
    case False{}:
      ol.plain(x, t, mode, nn, doc, out, e105, e100, e64, e108, e)

# first char `l`, else on
law ol.c_law:
  for +x: U32
  for +t: String
  for +mode: Outline.Mode
  for +nn: U32
  for +doc: List<&2, String>
  for +out: List<&2, Outline.Item>
  for +e105: {U32.is_eq(x, 105) == False{} : Bool}
  for +e100: {U32.is_eq(x, 100) == False{} : Bool}
  for +e64: {U32.is_eq(x, 64) == False{} : Bool}
  for +b: Bool
  for +e: {U32.is_eq(x, 108) == b : Bool}
  ol.goal(x, t, mode, nn, doc, out)

def ol.c_law(x, t, mode, nn, doc, out, e105, e100, e64, b, e):
  match b:
    case True{}:
      %Equal.sym(U32, x, 108, ol.ueq(x, 108, e)) : ol.goal(_, t, mode, nn, doc, out)
      ol.kw(String.starts_with(t, "aw "), Outline.LLaw{}, mode, SCon{Chr{108}, t}, nn, doc, out,
        Some{Outline.Item{Outline.ILaw{}, Laws.top.name(String.drop(SCon{Chr{108}, t}, 4n)), nn, "", "", ""}},
        ol.law_on(mode, SCon{Chr{108}, t}, nn, doc, out))
    case False{}:
      ol.c_ty(x, t, mode, nn, doc, out, e105, e100, e64, e, U32.is_eq(x, 116), {==})

# first char `@`, else on
law ol.c_at:
  for +x: U32
  for +t: String
  for +mode: Outline.Mode
  for +nn: U32
  for +doc: List<&2, String>
  for +out: List<&2, Outline.Item>
  for +e105: {U32.is_eq(x, 105) == False{} : Bool}
  for +e100: {U32.is_eq(x, 100) == False{} : Bool}
  for +b: Bool
  for +e: {U32.is_eq(x, 64) == b : Bool}
  ol.goal(x, t, mode, nn, doc, out)

def ol.c_at(x, t, mode, nn, doc, out, e105, e100, b, e):
  match b:
    case True{}:
      %Equal.sym(U32, x, 64, ol.ueq(x, 64, e)) : ol.goal(_, t, mode, nn, doc, out)
      ol.kw(String.starts_with(t, "unsafe def "), Outline.LDef{}, mode, SCon{Chr{64}, t}, nn, doc, out,
        Some{Outline.Item{Outline.IDef{}, Laws.top.name(String.drop(SCon{Chr{64}, t}, 12n)), nn, "", "", ""}},
        ol.def_on(mode, SCon{Chr{64}, t}, nn, doc, out, String.drop(SCon{Chr{64}, t}, 12n),
          Equal.cong(Bool, String, b => Outline.name(Bool.pick(String, b, String.drop(t, 11n), String.drop(t, 3n))),
            String.starts_with(t, SNil{}), True{},
            Equal.sym(Bool, True{}, String.starts_with(t, SNil{}), M1.starts_nil(t)))))
    case False{}:
      ol.c_law(x, t, mode, nn, doc, out, e105, e100, e, U32.is_eq(x, 108), {==})

# first char `d`, else on
law ol.c_def:
  for +x: U32
  for +t: String
  for +mode: Outline.Mode
  for +nn: U32
  for +doc: List<&2, String>
  for +out: List<&2, Outline.Item>
  for +e105: {U32.is_eq(x, 105) == False{} : Bool}
  for +b: Bool
  for +e: {U32.is_eq(x, 100) == b : Bool}
  ol.goal(x, t, mode, nn, doc, out)

def ol.c_def(x, t, mode, nn, doc, out, e105, b, e):
  match b:
    case True{}:
      %Equal.sym(U32, x, 100, ol.ueq(x, 100, e)) : ol.goal(_, t, mode, nn, doc, out)
      ol.kw(String.starts_with(t, "ef "), Outline.LDef{}, mode, SCon{Chr{100}, t}, nn, doc, out,
        Some{Outline.Item{Outline.IDef{}, Laws.top.name(String.drop(SCon{Chr{100}, t}, 4n)), nn, "", "", ""}},
        ol.def_on(mode, SCon{Chr{100}, t}, nn, doc, out, String.drop(SCon{Chr{100}, t}, 4n), {==}))
    case False{}:
      ol.c_at(x, t, mode, nn, doc, out, e105, e, U32.is_eq(x, 64), {==})

# first char `i`, else on
law ol.c_imp:
  for +x: U32
  for +t: String
  for +mode: Outline.Mode
  for +nn: U32
  for +doc: List<&2, String>
  for +out: List<&2, Outline.Item>
  for +b: Bool
  for +e: {U32.is_eq(x, 105) == b : Bool}
  ol.goal(x, t, mode, nn, doc, out)

def ol.c_imp(x, t, mode, nn, doc, out, b, e):
  match b:
    case True{}:
      %Equal.sym(U32, x, 105, ol.ueq(x, 105, e)) : ol.goal(_, t, mode, nn, doc, out)
      ol.kw(String.starts_with(t, "mport "), Outline.LImport{}, mode, SCon{Chr{105}, t}, nn, doc, out,
        Laws.top.import(List.filter(~String, ~Laws.top.word, String.split(SCon{Chr{105}, t}, ' ')), nn),
        ol.imp_on(mode, SCon{Chr{105}, t}, nn, doc, out))
    case False{}:
      ol.c_def(x, t, mode, nn, doc, out, e, U32.is_eq(x, 100), {==})

# one line: text inside a string opens nothing; a line of code opens what
# the spec says; either way the machine moves one line on
law ol.step:
  for +w: Bool
  for +ll: String
  for +mode: Outline.Mode
  for +nn: U32
  for +doc: List<&2, String>
  for +out: List<&2, Outline.Item>
  {shown(Outline.step(w, ll, Outline.St{mode, nn, doc, out}))
    == ol.adds(Bool.pick(Maybe<&2, Outline.Item>, w, None{}, Laws.top.head(ll, nn)), mode, out, nn) : Seen}

def ol.step(w, ll, mode, nn, doc, out):
  match w:
    case True{}:
      match mode:
        case Outline.Top{}:
          {==}
        case Outline.InType{}:
          {==}
        case Outline.Pending{_k, _nm, _l, _d, _sig}:
          {==}
    case False{}:
      match ll:
        case SNil{}:
          {==}
        case SCon{c, t}:
          match c:
            case Chr{+x}:
              ol.c_imp(x, t, mode, nn, doc, out, U32.is_eq(x, 105), {==})

# a list with an item picked on or not, by kind, name and line, reversed onto r
law ol.key_rev:
  for +h: Outline.Item
  for +ks: List<&2, Outline.Item>
  for +r: List<&2, Outline.Item>
  {List.reverse.go(&2, Outline.Item, Laws.top.key(h, ks), r)
    == List.reverse.go(&2, Outline.Item, ks, Laws.top.key(h, r)) : List<&2, Outline.Item>}

def ol.key_rev(h, ks, r):
  match h:
    case Outline.Item{+k, +nm, +ln, _s, _d, _p}:
      ol.rev_pick(Outline.Item, Laws.top.kept(k), Outline.Item{k, nm, ln, "", "", ""}, ks, r)

# the keys of a list reversed onto acc: its keys reversed onto acc's
law ol.keys_rev:
  for +xs: List<&2, Outline.Item>
  for +acc: List<&2, Outline.Item>
  {Laws.top.keys(List.reverse.go(&2, Outline.Item, xs, acc))
    == List.reverse.go(&2, Outline.Item, Laws.top.keys(xs), Laws.top.keys(acc)) : List<&2, Outline.Item>}

def ol.keys_rev(xs, acc):
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Equal.trans(List<&2, Outline.Item>,
        Laws.top.keys(List.reverse.go(&2, Outline.Item, t, h <> acc)),
        List.reverse.go(&2, Outline.Item, Laws.top.keys(t), Laws.top.key(h, Laws.top.keys(acc))),
        List.reverse.go(&2, Outline.Item, Laws.top.key(h, Laws.top.keys(t)), Laws.top.keys(acc)),
        ol.keys_rev(t, h <> acc),
        Equal.sym(List<&2, Outline.Item>,
          List.reverse.go(&2, Outline.Item, Laws.top.key(h, Laws.top.keys(t)), Laws.top.keys(acc)),
          List.reverse.go(&2, Outline.Item, Laws.top.keys(t), Laws.top.key(h, Laws.top.keys(acc))),
          ol.key_rev(h, Laws.top.keys(t), Laws.top.keys(acc))))

# an item, or none, put on a list reversed onto r: put on r instead
law ol.put_rev:
  for +mm: Maybe<&2, Outline.Item>
  for +ks: List<&2, Outline.Item>
  for +r: List<&2, Outline.Item>
  {List.reverse.go(&2, Outline.Item, Laws.top.put(mm, ks), r)
    == List.reverse.go(&2, Outline.Item, ks, Laws.top.put(mm, r)) : List<&2, Outline.Item>}

def ol.put_rev(mm, _ks, _r):
  match mm:
    case None{}:
      {==}
    case Some{_i}:
      {==}

# the keys a view holds
def ol.ks(vv: Seen) -> List<&2, Outline.Item>:
  match vv:
    case Seen{ks, _l}:
      ks

# the line a view is on
def ol.ln(vv: Seen) -> U32:
  match vv:
    case Seen{_ks, l}:
      l

# one line more: the keys the rest of the run lists follow the ones this
# line settles
law ol.run.arm:
  for +w: Bool
  for +ll: String
  for +t: List<&2, String>
  for +mode: Outline.Mode
  for +nn: U32
  for +doc: List<&2, String>
  for +out: List<&2, Outline.Item>
  for +r: List<&2, Bool>
  for ih: {Laws.top.keys(Outline.finish(Outline.run(t, Outline.step(w, ll, Outline.St{mode, nn, doc, out}), r)))
    == List.reverse.go(&2, Outline.Item, ol.ks(shown(Outline.step(w, ll, Outline.St{mode, nn, doc, out}))),
      Laws.top.spec(t, r, ol.ln(shown(Outline.step(w, ll, Outline.St{mode, nn, doc, out}))))) : List<&2, Outline.Item>}
  {Laws.top.keys(Outline.finish(Outline.run(t, Outline.step(w, ll, Outline.St{mode, nn, doc, out}), r)))
    == List.reverse.go(&2, Outline.Item, Laws.top.keys(Outline.flush(mode, out)),
      Laws.top.put(Bool.pick(Maybe<&2, Outline.Item>, w, None{}, Laws.top.head(ll, nn)),
        Laws.top.spec(t, r, (nn + 1 : U32)))) : List<&2, Outline.Item>}

def ol.run.arm(w, ll, t, mode, nn, doc, out, r, ih):
  Equal.trans(List<&2, Outline.Item>,
    Laws.top.keys(Outline.finish(Outline.run(t, Outline.step(w, ll, Outline.St{mode, nn, doc, out}), r))),
    List.reverse.go(&2, Outline.Item, ol.ks(shown(Outline.step(w, ll, Outline.St{mode, nn, doc, out}))),
      Laws.top.spec(t, r, ol.ln(shown(Outline.step(w, ll, Outline.St{mode, nn, doc, out}))))),
    List.reverse.go(&2, Outline.Item, Laws.top.keys(Outline.flush(mode, out)),
      Laws.top.put(Bool.pick(Maybe<&2, Outline.Item>, w, None{}, Laws.top.head(ll, nn)),
        Laws.top.spec(t, r, (nn + 1 : U32)))),
    ih,
    Equal.trans(List<&2, Outline.Item>,
      List.reverse.go(&2, Outline.Item, ol.ks(shown(Outline.step(w, ll, Outline.St{mode, nn, doc, out}))),
        Laws.top.spec(t, r, ol.ln(shown(Outline.step(w, ll, Outline.St{mode, nn, doc, out}))))),
      List.reverse.go(&2, Outline.Item,
        Laws.top.put(Bool.pick(Maybe<&2, Outline.Item>, w, None{}, Laws.top.head(ll, nn)),
          Laws.top.keys(Outline.flush(mode, out))),
        Laws.top.spec(t, r, (nn + 1 : U32))),
      List.reverse.go(&2, Outline.Item, Laws.top.keys(Outline.flush(mode, out)),
        Laws.top.put(Bool.pick(Maybe<&2, Outline.Item>, w, None{}, Laws.top.head(ll, nn)),
          Laws.top.spec(t, r, (nn + 1 : U32)))),
      Equal.cong(Seen, List<&2, Outline.Item>,
        vv => List.reverse.go(&2, Outline.Item, ol.ks(vv), Laws.top.spec(t, r, ol.ln(vv))),
        shown(Outline.step(w, ll, Outline.St{mode, nn, doc, out})),
        ol.adds(Bool.pick(Maybe<&2, Outline.Item>, w, None{}, Laws.top.head(ll, nn)), mode, out, nn),
        ol.step(w, ll, mode, nn, doc, out)),
      ol.put_rev(Bool.pick(Maybe<&2, Outline.Item>, w, None{}, Laws.top.head(ll, nn)),
        Laws.top.keys(Outline.flush(mode, out)), Laws.top.spec(t, r, (nn + 1 : U32)))))

# running the outline over the lines lists what the state has settled, then
# what the spec says the lines open
law ol.run:
  for +lines: List<&2, String>
  for +st: Outline.St
  for +ins: List<&2, Bool>
  {Laws.top.keys(Outline.finish(Outline.run(lines, st, ins)))
    == List.reverse.go(&2, Outline.Item, ol.ks(shown(st)), Laws.top.spec(lines, ins, ol.ln(shown(st))))
    : List<&2, Outline.Item>}

def ol.run(lines, st, ins):
  match lines:
    case Nil{}:
      match st:
        case Outline.St{mode, _nn, _doc, out}:
          ol.keys_rev(Outline.flush(mode, out), [])
    case Con{+ll, +t}:
      match st:
        case Outline.St{+mode, +nn, +doc, +out}:
          match ins:
            case Nil{}:
              ol.run.arm(False{}, ll, t, mode, nn, doc, out, [],
                ol.run(t, Outline.step(False{}, ll, Outline.St{mode, nn, doc, out}), []))
            case Con{+h, +r}:
              ol.run.arm(h, ll, t, mode, nn, doc, out, r,
                ol.run(t, Outline.step(h, ll, Outline.St{mode, nn, doc, out}), r))

def Laws.outline(text, toks):
  Equal.trans(List<&2, Outline.Item>,
    Laws.top.keys(Outline.of_tokens(text, toks)),
    Laws.top.spec(String.lines(text), Outline.inside(toks), 0),
    Laws.top.spec(String.lines(text), False{} <> Laws.top.strung(toks), 0),
    ol.run(String.lines(text), Outline.St{Outline.Top{}, 0, [], []}, Outline.inside(toks)),
    Equal.cong(List<&2, Bool>, List<&2, Outline.Item>, x => Laws.top.spec(String.lines(text), x, 0),
      Outline.inside(toks), False{} <> Laws.top.strung(toks), ol.flags(toks)))

def Laws.undoc_drops_hash_and_space(ss, e):
  %Equal.sym(Bool, String.starts_with(ss, "# "), True{}, e) :
    {Bool.pick(String, _, String.drop(ss, 2n),
      Bool.pick(String, String.starts_with(ss, "#"), String.drop(ss, 1n), ss)) == String.drop(ss, 2n) : String}
  {==}

def Laws.undoc_drops_a_bare_hash(ss, e1, e2):
  %Equal.sym(Bool, String.starts_with(ss, "# "), False{}, e1) :
    {Bool.pick(String, _, String.drop(ss, 2n),
      Bool.pick(String, String.starts_with(ss, "#"), String.drop(ss, 1n), ss)) == String.drop(ss, 1n) : String}
  %Equal.sym(Bool, String.starts_with(ss, "#"), True{}, e2) :
    {Bool.pick(String, _, String.drop(ss, 1n), ss) == String.drop(ss, 1n) : String}
  {==}

def Laws.undoc_keeps_other_lines(ss, e1, e2):
  %Equal.sym(Bool, String.starts_with(ss, "# "), False{}, e1) :
    {Bool.pick(String, _, String.drop(ss, 2n),
      Bool.pick(String, String.starts_with(ss, "#"), String.drop(ss, 1n), ss)) == ss : String}
  %Equal.sym(Bool, String.starts_with(ss, "#"), False{}, e2) :
    {Bool.pick(String, _, String.drop(ss, 1n), ss) == ss : String}
  {==}

def Laws.doc_text_joins_lines(_doc):
  {==}

def Laws.sig_text_joins_lines(_sig):
  {==}
