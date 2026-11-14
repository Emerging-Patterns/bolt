# and/compare facts for the inert text cut and its token marks
import Base
import ../../src/syntax/lex.bend as Lex
import ../../src/finding.bend as F
import ../../src/rules/tokens.bend as T
import ../../laws/defs/InertText.bend as D1
import ./RoleProofPicked.bend as M1

# Inert text (laws/CodeRulesIgnoreCommentsAndStrings.bend). Each rule gives the same findings on a
# source read with its comments and strings cut (Laws.inert.toks,
# Laws.inert.node) as on the source; two sources that read the same that way
# then have the same findings. A rule tests a token's kind before its text,
# or compares the text of a token of any kind with a name or a keyword,
# which never starts with `"` or `#`: a string's text, cut or not, never
# equals it. A kind is split only where the rule itself matches on one.

# Unit for False, Empty for True
def inert.false_ty(b: Bool) -> Type:
  match b:
    case False{}: Unit
    case True{}: Empty

# False is never True
law inert.false_true:
  for e: {False{} == True{} : Bool}
  Empty

def inert.false_true(e):
  %e : inert.false_ty(_)
  Unit{}

# the left of an and that holds holds
law inert.and_l:
  for a: Bool
  for -b: Bool
  for e: {Bool.and(a, b) == True{} : Bool}
  {a == True{} : Bool}

def inert.and_l(a, _b, e):
  match a:
    case True{}: {==}
    case False{}: Empty.absurd({False{} == True{} : Bool}, inert.false_true(e))

# the right of an and that holds holds
law inert.and_r:
  for a: Bool
  for -b: Bool
  for e: {Bool.and(a, b) == True{} : Bool}
  {b == True{} : Bool}

def inert.and_r(a, b, e):
  match a:
    case True{}: e
    case False{}: Empty.absurd({b == True{} : Bool}, inert.false_true(e))

# two facts that hold make their and hold
law inert.and_both:
  for -a: Bool
  for -b: Bool
  for ea: {a == True{} : Bool}
  for eb: {b == True{} : Bool}
  {Bool.and(a, b) == True{} : Bool}

def inert.and_both(a, b, ea, eb):
  %Equal.sym(Bool, a, True{}, ea) : {Bool.and(_, b) == True{} : Bool}
  eb

# Unit for LT and GT, Empty for EQ
def inert.cmp_ty(c: Cmp) -> Type:
  match c:
    case LT{}: Unit
    case EQ{}: Empty
    case GT{}: Unit

# a comparison that is EQ is not LT
law inert.lt_eq:
  for e: {LT{} == EQ{} : Cmp}
  Empty

def inert.lt_eq(e):
  %e : inert.cmp_ty(_)
  Unit{}

# a comparison that is EQ is not GT
law inert.gt_eq:
  for e: {GT{} == EQ{} : Cmp}
  Empty

def inert.gt_eq(e):
  %e : inert.cmp_ty(_)
  Unit{}

# a word comparison that ends EQ was EQ on the bits below
law inert.fin_eq:
  for t: Cmp
  for -ab: Bool
  for -b: Bool
  for e: {Word.cmp.fin(ab, b, t) == EQ{} : Cmp}
  {t == EQ{} : Cmp}

def inert.fin_eq(t, _ab, _bb, e):
  match t:
    case LT{}: Empty.absurd({LT{} == EQ{} : Cmp}, inert.lt_eq(e))
    case EQ{}: {==}
    case GT{}: Empty.absurd({GT{} == EQ{} : Cmp}, inert.gt_eq(e))

# a word comparison that ends EQ had the same top bit
law inert.fin_bit:
  for t: Cmp
  for ab: Bool
  for b: Bool
  for e: {Word.cmp.fin(ab, b, t) == EQ{} : Cmp}
  {ab == b : Bool}

def inert.fin_bit(t, ab, b, e):
  match t:
    case LT{}: Empty.absurd({ab == b : Bool}, inert.lt_eq(e))
    case GT{}: Empty.absurd({ab == b : Bool}, inert.gt_eq(e))
    case EQ{}:
      match ab b:
        case False{} False{}: {==}
        case False{} True{}: Empty.absurd({False{} == True{} : Bool}, inert.lt_eq(e))
        case True{} False{}: Empty.absurd({True{} == False{} : Bool}, inert.gt_eq(e))
        case True{} True{}: {==}

# two words that compare EQ are the same word
law inert.word_eq:
  for +n: Nat
  for a: Word(n)
  for b: Word(n)
  for +e: {Word.cmp(n, a, b) == EQ{} : Cmp}
  {a == b : Word(n)}

def inert.word_eq(n, a, b, e):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}: {==}
    case 1n+p:
      match a b:
        case WCon{+ab, +at} WCon{+bb, +bt}:
          hb = inert.fin_bit(Word.cmp(p, at, bt), ab, bb, e)
          ht = inert.word_eq(p, at, bt, inert.fin_eq(Word.cmp(p, at, bt), ab, bb, e))
          %hb : {WCon{ab, at} == WCon{_, bt} : Word(1n+p)}
          %ht : {WCon{ab, at} == WCon{ab, _} : Word(1n+p)}
          {==}

# two U32s that compare EQ are the same
law inert.u32_eq:
  for x: U32
  for y: U32
  for e: {U32.cmp(x, y) == EQ{} : Cmp}
  {x == y : U32}

def inert.u32_eq(x, y, e):
  match x y:
    case U32{wx} U32{wy}: Equal.cong(Word(32n), U32, w => U32{w}, wx, wy, inert.word_eq(32n, wx, wy, e))

# a marked char and an unmarked one never compare EQ
law inert.differ:
  for c: Cmp
  for +x: U32
  for +y: U32
  for ec: {U32.cmp(x, y) == c : Cmp}
  for ex: {D1.inert.mark(Chr{x}) == True{} : Bool}
  for ey: {D1.inert.mark(Chr{y}) == False{} : Bool}
  {Cmp.is_eq(c) == False{} : Bool}

def inert.differ(c, x, y, ec, ex, ey):
  match c:
    case LT{}: {==}
    case GT{}: {==}
    case EQ{}:
      +my = Equal.trans(Bool, D1.inert.mark(Chr{y}), D1.inert.mark(Chr{x}), True{},
        Equal.cong(U32, Bool, z => D1.inert.mark(Chr{z}), y, x, Equal.sym(U32, x, y, inert.u32_eq(x, y, ec))), ex)
      Empty.absurd({Cmp.is_eq(EQ{}) == False{} : Bool}, inert.false_true(Equal.trans(Bool, False{},
        D1.inert.mark(Chr{y}), True{}, Equal.sym(Bool, D1.inert.mark(Chr{y}), False{}, ey), my)))

# a string comparison whose first chars differ is not equal, whatever follows
law inert.fin_false:
  for c: Cmp
  for r: String
  for ys: String
  for ec: {Cmp.is_eq(c) == False{} : Bool}
  {Cmp.is_eq(String.order.go(r, ys, c)) == False{} : Bool}

def inert.fin_false(c, r, ys, ec):
  match c:
    case LT{}:
      %Equal.sym(Cmp, String.order.go(r, ys, LT{}), LT{}, M1.unsafe.go_lt(r, ys)) :
        {Cmp.is_eq(_) == False{} : Bool}
      {==}
    case GT{}:
      %Equal.sym(Cmp, String.order.go(r, ys, GT{}), GT{}, M1.unsafe.go_gt(r, ys)) :
        {Cmp.is_eq(_) == False{} : Bool}
      {==}
    case EQ{}:
      Empty.absurd({Cmp.is_eq(String.order.go(r, ys, EQ{})) == False{} : Bool},
        inert.false_true(Equal.sym(Bool, True{}, False{}, ec)))

# a text with a marked first char is never equal to one with an unmarked one
law inert.neq.con:
  for h: Char
  for r: String
  for y: Char
  for ys: String
  for et: {D1.inert.mark(h) == True{} : Bool}
  for ex: {D1.inert.mark(y) == False{} : Bool}
  {String.eq(SCon{h, r}, SCon{y, ys}) == False{} : Bool}

def inert.neq.con(h, r, y, ys, et, ex):
  match h y:
    case Chr{+a} Chr{+b}:
      inert.fin_false(U32.cmp(a, b), r, ys, inert.differ(U32.cmp(a, b), a, b, {==}, et, ex))

# a marked text is never equal to an unmarked one
law inert.neq:
  for t: String
  for x: String
  for et: {D1.inert.marked(t) == True{} : Bool}
  for ex: {D1.inert.marked(x) == False{} : Bool}
  {String.eq(t, x) == False{} : Bool}

def inert.neq(t, x, et, ex):
  match t x:
    case SNil{} x: Empty.absurd({String.eq(SNil{}, x) == False{} : Bool}, inert.false_true(et))
    case SCon{Chr{_a}, r} SNil{}: {==}
    case SCon{h, r} SCon{y, ys}: inert.neq.con(h, r, y, ys, et, ex)

# a text cut to its first char is marked when the text is
law inert.cut_marked:
  for t: String
  for et: {D1.inert.marked(t) == True{} : Bool}
  {D1.inert.marked(D1.inert.cut(t)) == True{} : Bool}

def inert.cut_marked(t, et):
  match t:
    case SNil{}: et
    case SCon{h, r}: et

# a token's text read that way compares with an unmarked text as it did
law inert.eq_keep:
  for b: Bool
  for +t: String
  for +x: String
  for +ef: {D1.inert.fits.go(b, t) == True{} : Bool}
  for +ex: {D1.inert.marked(x) == False{} : Bool}
  {String.eq(D1.inert.keep(b, t), x) == String.eq(t, x) : Bool}

def inert.eq_keep(b, t, x, ef, ex):
  match b:
    case False{}: {==}
    case True{}:
      Equal.trans(Bool, String.eq(D1.inert.cut(t), x), False{}, String.eq(t, x),
        inert.neq(D1.inert.cut(t), x, inert.cut_marked(t, ef), ex),
        Equal.sym(Bool, String.eq(t, x), False{}, inert.neq(t, x, ef, ex)))

# two sources whose readings agree, each reading giving what its source
# gives, give the same
law inert.via:
  for -A: Data
  for -f: A -> List<&2, F.Finding>
  for -a: A
  for -b: A
  for -ca: A
  for -cb: A
  for ea: {f(ca) == f(a) : List<&2, F.Finding>}
  for eb: {f(cb) == f(b) : List<&2, F.Finding>}
  for e: {ca == cb : A}
  {f(a) == f(b) : List<&2, F.Finding>}

def inert.via(A, f, a, b, ca, cb, ea, eb, e):
  Equal.trans(List<&2, F.Finding>, f(a), f(ca), f(b), Equal.sym(List<&2, F.Finding>, f(ca), f(a), ea),
    Equal.trans(List<&2, F.Finding>, f(ca), f(cb), f(b), Equal.cong(A, List<&2, F.Finding>, f, ca, cb, e), eb))

# put
# ---

# reading the tokens that way commutes with a pick between two lists that
# differ by one token in front
law inert.put.pick:
  for b: Bool
  for +x: Lex.Tok
  for +xs: List<&2, Lex.Tok>
  {D1.inert.toks(Bool.pick(List<&2, Lex.Tok>, b, x <> xs, xs))
    == Bool.pick(List<&2, Lex.Tok>, b, D1.inert.tok(x) <> D1.inert.toks(xs),
      D1.inert.toks(xs)) : List<&2, Lex.Tok>}

def inert.put.pick(b, _x, _xs):
  match b:
    case True{}: {==}
    case False{}: {==}

# the significant tokens of the tokens read that way are the significant
# tokens read that way
law inert.put.sig:
  for ts: List<&2, Lex.Tok>
  {T.sig(D1.inert.toks(ts)) == D1.inert.toks(T.sig(ts)) : List<&2, Lex.Tok>}

def inert.put.sig(ts):
  match ts:
    case Nil{}: {==}
    case Con{Lex.Tok{+k, +t, +l, +c}, +rest}:
      +x = {Lex.Tok{k, D1.inert.keep(D1.inert.blanks(k), t), l, c} : Lex.Tok}
      +cs = D1.inert.toks(T.sig(rest))
      %Equal.sym(List<&2, Lex.Tok>, T.sig(D1.inert.toks(rest)), cs, inert.put.sig(rest)) :
        {Bool.pick(List<&2, Lex.Tok>, Lex.significant(k), x <> _, _) == D1.inert.toks(T.sig(Lex.Tok{k, t, l,
          c} <> rest))
          : List<&2, Lex.Tok>}
      Equal.sym(List<&2, Lex.Tok>, D1.inert.toks(T.sig(Lex.Tok{k, t, l, c} <> rest)),
        Bool.pick(List<&2, Lex.Tok>, Lex.significant(k), x <> cs, cs),
        inert.put.pick(Lex.significant(k), Lex.Tok{k, t, l, c}, T.sig(rest)))

# a pick between two lists that differ by one token in front keeps the
# tokens as the lexer makes them
law inert.put.pick_ok:
  for b: Bool
  for +x: Lex.Tok
  for +xs: List<&2, Lex.Tok>
  for e: {Bool.and(D1.inert.fits(x), D1.inert.oks(xs)) == True{} : Bool}
  for er: {D1.inert.oks(xs) == True{} : Bool}
  {D1.inert.oks(Bool.pick(List<&2, Lex.Tok>, b, x <> xs, xs)) == True{} : Bool}

def inert.put.pick_ok(b, _x, _xs, e, er):
  match b:
    case True{}: e
    case False{}: er

# the significant tokens of tokens as the lexer makes them are too
law inert.put.sig_ok:
  for ts: List<&2, Lex.Tok>
  for +e: {D1.inert.oks(ts) == True{} : Bool}
  {D1.inert.oks(T.sig(ts)) == True{} : Bool}

def inert.put.sig_ok(ts, e):
  match ts:
    case Nil{}: {==}
    case Con{Lex.Tok{+k, +t, +l, +c}, +rest}:
      +h = {Lex.Tok{k, t, l, c} : Lex.Tok}
      +er = inert.put.sig_ok(rest, inert.and_r(D1.inert.fits(h), D1.inert.oks(rest), e))
      inert.put.pick_ok(Lex.significant(k), h, T.sig(rest),
        inert.and_both(D1.inert.fits(h), D1.inert.oks(T.sig(rest)), inert.and_l(D1.inert.fits(h),
          D1.inert.oks(rest), e), er), er)
