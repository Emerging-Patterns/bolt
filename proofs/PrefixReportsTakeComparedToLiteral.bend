# proofs of laws/PrefixReportsTakeComparedToLiteral.bend
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/rules/tokens.bend as T
import ../src/paths.bend as Paths
import ../src/rules/suspicious/prefix.bend as Prefix
import ../laws/PrefixReportsTakeComparedToLiteral.bend as Laws
import ./lemmas/PutEarlyStop.bend as M1
import ./lemmas/PrefixLength.bend as M2
import ../laws/defs/PrefixLength.bend as D1

# prefix
# ------

# does the maybe hold a message?
def prefix.some(m: Maybe<&2, String>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{_x}:
      True{}

# the tokens after a scanned argument, its text dropped
def prefix.rest(ma: Maybe<&2, Prefix.Arg>) -> Maybe<&2, List<&2, Lex.Tok>>:
  match ma:
    case None{}:
      None{}
    case Some{Prefix.Arg{_s, r}}:
      Some{r}

# the rule's step of the scan is the law's
law prefix.step:
  for k: Lex.TokKind
  for d: Nat
  {Prefix.skip.step(k, d) == Laws.prefix_step(k, d) : Prefix.Skip}

def prefix.step(k, d):
  match k:
    case Lex.TName{}:
      {==}
    case Lex.TUpper{}:
      {==}
    case Lex.TDotted{}:
      {==}
    case Lex.TWild{}:
      {==}
    case Lex.TKey{}:
      {==}
    case Lex.TNum{}:
      {==}
    case Lex.TStr{}:
      {==}
    case Lex.TChar{}:
      {==}
    case Lex.TComment{}:
      {==}
    case Lex.TSpace{}:
      {==}
    case Lex.TNewline{}:
      {==}
    case Lex.TOp{}:
      {==}
    case Lex.TColon{}:
      {==}
    case Lex.TEq{}:
      {==}
    case Lex.TBind{}:
      {==}
    case Lex.TArrow{}:
      {==}
    case Lex.TLam{}:
      {==}
    case Lex.TAll{}:
      {==}
    case Lex.TAmp{}:
      {==}
    case Lex.TOpen{}:
      {==}
    case Lex.TClose{}:
      match d:
        case 0n:
          {==}
        case 1n+_p:
          {==}
    case Lex.TComma{}:
      match d:
        case 0n:
          {==}
        case 1n+_p:
          {==}

# the rule's scan of an argument ends where the law's does
law prefix.skip:
  for toks: List<&2, Lex.Tok>
  for sk: Prefix.Skip
  for +acc: List<&2, String>
  {prefix.rest(Prefix.skip(toks, sk, acc)) == Laws.prefix_skip(toks, sk) : Maybe<&2, List<&2, Lex.Tok>>}

def prefix.skip(toks, sk, acc):
  match toks:
    case Nil{}:
      {==}
    case Con{Lex.Tok{+k, +t, +l, +c}, +rest}:
      match sk:
        case Prefix.SComma{}:
          {==}
        case Prefix.SClose{}:
          {==}
        case Prefix.SGo{+d}:
          +nx = Prefix.skip.step(k, d)
          +acc2 = {Prefix.skip.piece(nx, k, t) <> acc : List<&2, String>}
          Equal.trans(Maybe<&2, List<&2, Lex.Tok>>, prefix.rest(Prefix.skip(rest, nx, acc2)), Laws.prefix_skip(rest,
            nx),
            Laws.prefix_skip(rest, Laws.prefix_step(k, d)), prefix.skip(rest, nx, acc2),
            Equal.cong(Prefix.Skip, Maybe<&2, List<&2, Lex.Tok>>, z => Laws.prefix_skip(rest, z), nx,
              Laws.prefix_step(k, d), prefix.step(k, d)))

# the rule's dotted test is the law's
law prefix.dotted:
  for k: Lex.TokKind
  {Prefix.dotted(k) == Laws.prefix_dotted(k) : Bool}

def prefix.dotted(k):
  match k:
    case Lex.TName{}:
      {==}
    case Lex.TUpper{}:
      {==}
    case Lex.TDotted{}:
      {==}
    case Lex.TWild{}:
      {==}
    case Lex.TKey{}:
      {==}
    case Lex.TNum{}:
      {==}
    case Lex.TStr{}:
      {==}
    case Lex.TChar{}:
      {==}
    case Lex.TComment{}:
      {==}
    case Lex.TSpace{}:
      {==}
    case Lex.TNewline{}:
      {==}
    case Lex.TOp{}:
      {==}
    case Lex.TColon{}:
      {==}
    case Lex.TEq{}:
      {==}
    case Lex.TBind{}:
      {==}
    case Lex.TArrow{}:
      {==}
    case Lex.TLam{}:
      {==}
    case Lex.TAll{}:
      {==}
    case Lex.TAmp{}:
      {==}
    case Lex.TOpen{}:
      {==}
    case Lex.TClose{}:
      {==}
    case Lex.TComma{}:
      {==}

# a message picked when b holds: holds one exactly when b does
law prefix.some1:
  for b: Bool
  for -x: String
  {prefix.some(Bool.pick(Maybe<&2, String>, b, Some{x}, None{})) == b : Bool}

def prefix.some1(b, _x):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the same, b equal to c
law prefix.some_eq:
  for b: Bool
  for c: Bool
  for -x: String
  for e: {b == c : Bool}
  {prefix.some(Bool.pick(Maybe<&2, String>, b, Some{x}, None{})) == c : Bool}

def prefix.some_eq(b, c, x, e):
  Equal.trans(Bool, prefix.some(Bool.pick(Maybe<&2, String>, b, Some{x}, None{})), b, c, prefix.some1(b, x), e)

# the rule's take-first end test is the law's
law prefix.ok_a:
  for +t6: String
  for +t7: String
  for +t8: String
  for +k9: Lex.TokKind
  for +t9: String
  for +t10: String
  {Prefix.tail_a.ok(t6, t7, t8, k9, t9, t10) == Bool.and(String.eq(t7, ")"), Bool.and(String.eq(t8, ","),
    Bool.and(Lex.is_str(k9), Bool.and(String.eq(t10, ")"), D1.prefix_fits(t6, t9))))) : Bool}

def prefix.ok_a(t6, t7, t8, k9, t9, t10):
  Equal.cong(Bool, Bool, z => Bool.and(String.eq(t7, ")"), Bool.and(String.eq(t8, ","), Bool.and(Lex.is_str(k9),
    Bool.and(String.eq(t10, ")"), z)))), Prefix.fits(t6, t9), D1.prefix_fits(t6, t9), M2.prefix.fits(t6, t9))

# the rule's literal-first end test is the law's
law prefix.ok_b:
  for +t8: String
  for +t9: String
  for +t10: String
  for +lit: String
  {Prefix.tail_b.ok(t8, t9, t10, lit) == Bool.and(String.eq(t9, ")"), Bool.and(String.eq(t10, ")"),
    D1.prefix_fits(t8, lit))) : Bool}

def prefix.ok_b(t8, t9, t10, lit):
  Equal.cong(Bool, Bool, z => Bool.and(String.eq(t9, ")"), Bool.and(String.eq(t10, ")"), z)), Prefix.fits(t8, lit),
    D1.prefix_fits(t8, lit), M2.prefix.fits(t8, lit))

# the rule's take-first end is the law's
law prefix.tail_a:
  for ma: Maybe<&2, Prefix.Arg>
  {prefix.some(Prefix.tail_a(ma)) == Laws.prefix_tail_a(prefix.rest(ma)) : Bool}

def prefix.tail_a(ma):
  match ma:
    case None{}:
      {==}
    case Some{Prefix.Arg{+s, r}}:
      match r:
        case Nil{}:
          {==}
        case Con{Lex.Tok{k6, +a6, l6, c6}, r6}:
          match r6:
            case Nil{}:
              {==}
            case Con{Lex.Tok{k7, +a7, l7, c7}, r7}:
              match r7:
                case Nil{}:
                  {==}
                case Con{Lex.Tok{k8, +a8, l8, c8}, r8}:
                  match r8:
                    case Nil{}:
                      {==}
                    case Con{Lex.Tok{+k9, +a9, l9, c9}, r9}:
                      match r9:
                        case Nil{}:
                          {==}
                        case Con{Lex.Tok{k10, +a10, l10, c10}, r10}:
                          prefix.some_eq(Prefix.tail_a.ok(a6, a7, a8, k9, a9, a10), Bool.and(String.eq(a7, ")"),
                            Bool.and(String.eq(a8, ","), Bool.and(Lex.is_str(k9), Bool.and(String.eq(a10, ")"),
                              D1.prefix_fits(a6, a9))))),
                            Prefix.say(s, a6, a9), prefix.ok_a(a6, a7, a8, k9, a9, a10))

# the rule's literal-first end is the law's
law prefix.tail_b:
  for ma: Maybe<&2, Prefix.Arg>
  for +lit: String
  {prefix.some(Prefix.tail_b(ma, lit)) == Laws.prefix_tail_b(prefix.rest(ma), lit) : Bool}

def prefix.tail_b(ma, lit):
  match ma:
    case None{}:
      {==}
    case Some{Prefix.Arg{+s, r}}:
      match r:
        case Nil{}:
          {==}
        case Con{Lex.Tok{k8, +a8, l8, c8}, r8}:
          match r8:
            case Nil{}:
              {==}
            case Con{Lex.Tok{k9, +a9, l9, c9}, r9}:
              match r9:
                case Nil{}:
                  {==}
                case Con{Lex.Tok{k10, +a10, l10, c10}, r10}:
                  prefix.some_eq(Prefix.tail_b.ok(a8, a9, a10, lit), Bool.and(String.eq(a9, ")"),
                    Bool.and(String.eq(a10, ")"),
                    D1.prefix_fits(a8, lit))), Prefix.say(s, a8, lit), prefix.ok_b(a8, a9, a10, lit))

# the take-first shape after its head, the head's test b: the law's
law prefix.go_a:
  for b: Bool
  for +r3: List<&2, Lex.Tok>
  {prefix.some(Prefix.at_a.go(b, r3)) == Bool.and(b, Laws.prefix_tail_a(Laws.prefix_skip(r3, Prefix.SGo{0n})))
    : Bool}

def prefix.go_a(b, r3):
  match b:
    case True{}:
      +sk = Prefix.skip(r3, Prefix.SGo{0n}, [])
      Equal.trans(Bool, prefix.some(Prefix.tail_a(sk)), Laws.prefix_tail_a(prefix.rest(sk)),
        Laws.prefix_tail_a(Laws.prefix_skip(r3, Prefix.SGo{0n})), prefix.tail_a(sk),
        Equal.cong(Maybe<&2, List<&2, Lex.Tok>>, Bool, z => Laws.prefix_tail_a(z), prefix.rest(sk),
          Laws.prefix_skip(r3, Prefix.SGo{0n}), prefix.skip(r3, Prefix.SGo{0n}, [])))
    case False{}:
      {==}

# the literal-first shape after its head, the head's test b: the law's
law prefix.go_b:
  for b: Bool
  for +r5: List<&2, Lex.Tok>
  for +lit: String
  {prefix.some(Prefix.at_b.go(b, r5, lit)) == Bool.and(b, Laws.prefix_tail_b(Laws.prefix_skip(r5, Prefix.SGo{0n}),
    lit)) : Bool}

def prefix.go_b(b, r5, lit):
  match b:
    case True{}:
      +sk = Prefix.skip(r5, Prefix.SGo{0n}, [])
      Equal.trans(Bool, prefix.some(Prefix.tail_b(sk, lit)), Laws.prefix_tail_b(prefix.rest(sk), lit),
        Laws.prefix_tail_b(Laws.prefix_skip(r5, Prefix.SGo{0n}), lit), prefix.tail_b(sk, lit),
        Equal.cong(Maybe<&2, List<&2, Lex.Tok>>, Bool, z => Laws.prefix_tail_b(z, lit), prefix.rest(sk),
          Laws.prefix_skip(r5, Prefix.SGo{0n}), prefix.skip(r5, Prefix.SGo{0n}, [])))
    case False{}:
      {==}

# an and whose first test is rewritten
law prefix.and_l:
  for p: Bool
  for p2: Bool
  for q: Bool
  for e: {p == p2 : Bool}
  {Bool.and(p, q) == Bool.and(p2, q) : Bool}

def prefix.and_l(p, p2, q, e):
  Equal.cong(Bool, Bool, z => Bool.and(z, q), p, p2, e)

# the take-first shape, its head's dotted test the law's: the law's
law prefix.go_a2:
  for p: Bool
  for p2: Bool
  for q: Bool
  for +r3: List<&2, Lex.Tok>
  for e: {p == p2 : Bool}
  {prefix.some(Prefix.at_a.go(Bool.and(p, q), r3))
    == Bool.and(Bool.and(p2, q), Laws.prefix_tail_a(Laws.prefix_skip(r3, Prefix.SGo{0n}))) : Bool}

def prefix.go_a2(p, _p2, q, r3, e):
  %e : {prefix.some(Prefix.at_a.go(Bool.and(p, q), r3))
    == Bool.and(Bool.and(_, q), Laws.prefix_tail_a(Laws.prefix_skip(r3, Prefix.SGo{0n}))) : Bool}
  prefix.go_a(Bool.and(p, q), r3)

# the literal-first shape, its head's dotted test the law's: the law's
law prefix.go_b2:
  for p: Bool
  for p2: Bool
  for q: Bool
  for +r5: List<&2, Lex.Tok>
  for +lit: String
  for e: {p == p2 : Bool}
  {prefix.some(Prefix.at_b.go(Bool.and(p, q), r5, lit))
    == Bool.and(Bool.and(p2, q), Laws.prefix_tail_b(Laws.prefix_skip(r5, Prefix.SGo{0n}), lit)) : Bool}

def prefix.go_b2(p, _p2, q, r5, lit, e):
  %e : {prefix.some(Prefix.at_b.go(Bool.and(p, q), r5, lit))
    == Bool.and(Bool.and(_, q), Laws.prefix_tail_b(Laws.prefix_skip(r5, Prefix.SGo{0n}), lit)) : Bool}
  prefix.go_b(Bool.and(p, q), r5, lit)

# the rule's take-first test of a run is the law's
law prefix.at_a:
  for +k0: Lex.TokKind
  for +t0: String
  for toks: List<&2, Lex.Tok>
  {prefix.some(Prefix.at_a(k0, t0, toks)) == Laws.prefix_a(k0, t0, toks) : Bool}

def prefix.at_a(k0, t0, toks):
  match toks:
    case Nil{}:
      {==}
    case Con{Lex.Tok{k1, +a1, l1, c1}, r1}:
      match r1:
        case Nil{}:
          {==}
        case Con{Lex.Tok{k2, +a2, l2, c2}, r2}:
          match r2:
            case Nil{}:
              {==}
            case Con{Lex.Tok{k3, +a3, l3, c3}, r3}:
              prefix.go_a2(Prefix.dotted(k0), Laws.prefix_dotted(k0),
                Bool.and(String.eq(t0, "String.eq"), Bool.and(String.eq(a1, "("), Bool.and(String.eq(a3, "("),
                  String.eq(a2, "String.take")))),
                r3, prefix.dotted(k0))

# the rule's literal-first test of a run is the law's
law prefix.at_b:
  for +k0: Lex.TokKind
  for +t0: String
  for toks: List<&2, Lex.Tok>
  {prefix.some(Prefix.at_b(k0, t0, toks)) == Laws.prefix_b(k0, t0, toks) : Bool}

def prefix.at_b(k0, t0, toks):
  match toks:
    case Nil{}:
      {==}
    case Con{Lex.Tok{k1, +a1, l1, c1}, r1}:
      match r1:
        case Nil{}:
          {==}
        case Con{Lex.Tok{+k2, +a2, l2, c2}, r2}:
          match r2:
            case Nil{}:
              {==}
            case Con{Lex.Tok{k3, +a3, l3, c3}, r3}:
              match r3:
                case Nil{}:
                  {==}
                case Con{Lex.Tok{k4, +a4, l4, c4}, r4}:
                  match r4:
                    case Nil{}:
                      {==}
                    case Con{Lex.Tok{k5, +a5, l5, c5}, r5}:
                      prefix.go_b2(Prefix.dotted(k0), Laws.prefix_dotted(k0),
                        Bool.and(String.eq(t0, "String.eq"), Bool.and(String.eq(a1, "("), Bool.and(Lex.is_str(k2),
                          Bool.and(String.eq(a3, ","), Bool.and(String.eq(a4, "String.take"), String.eq(a5, "(")))))),
                        r5, a2, prefix.dotted(k0))

# either message holds one when either does
law prefix.either:
  for ma: Maybe<&2, String>
  for mb: Maybe<&2, String>
  {prefix.some(Prefix.either(ma, mb)) == Bool.or(prefix.some(ma), prefix.some(mb)) : Bool}

def prefix.either(ma, _mb):
  match ma:
    case None{}:
      {==}
    case Some{_x}:
      {==}

# an or of two tests each rewritten
law prefix.or2:
  for p: Bool
  for p2: Bool
  for q: Bool
  for q2: Bool
  for e1: {p == p2 : Bool}
  for e2: {q == q2 : Bool}
  {Bool.or(p, q) == Bool.or(p2, q2) : Bool}

def prefix.or2(p, _p2, q, q2, e1, e2):
  %e1 : {Bool.or(p, q) == Bool.or(_, q2) : Bool}
  %e2 : {Bool.or(p, q) == Bool.or(p, _) : Bool}
  {==}

# the rule's test of a run is the law's
law prefix.at:
  for +k0: Lex.TokKind
  for +t0: String
  for +toks: List<&2, Lex.Tok>
  {prefix.some(Prefix.at(k0, t0, toks)) == Laws.prefix_at(k0, t0, toks) : Bool}

def prefix.at(k0, t0, toks):
  +ma = Prefix.at_a(k0, t0, toks)
  +mb = Prefix.at_b(k0, t0, toks)
  Equal.trans(Bool, prefix.some(Prefix.either(ma, mb)), Bool.or(prefix.some(ma), prefix.some(mb)),
    Bool.or(Laws.prefix_a(k0, t0, toks), Laws.prefix_b(k0, t0, toks)), prefix.either(ma, mb),
    prefix.or2(prefix.some(ma), Laws.prefix_a(k0, t0, toks), prefix.some(mb), Laws.prefix_b(k0, t0, toks),
      prefix.at_a(k0, t0, toks), prefix.at_b(k0, t0, toks)))

# a finding in front when the maybe holds a message adds one to the count
law prefix.hit:
  for mm: Maybe<&2, String>
  for -path: String
  for -l: U32
  for -c: U32
  for -more: List<&2, F.Finding>
  for -m: Nat
  for ih: {List.length(&2, F.Finding, more) == m : Nat}
  {List.length(&2, F.Finding, Prefix.hit(mm, path, l, c, more)) == Bool.pick(Nat, prefix.some(mm), 1n+m, m) : Nat}

def prefix.hit(mm, _path, _ll, _cc, more, m, ih):
  match mm:
    case None{}:
      ih
    case Some{_x}:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, F.Finding, more), m, ih)

# prefix's walk counts the runs
law prefix.walk:
  for toks: List<&2, Lex.Tok>
  for +path: String
  {List.length(&2, F.Finding, Prefix.walk(toks, path)) == Laws.prefix_count(toks) : Nat}

def prefix.walk(toks, path):
  match toks:
    case Nil{}:
      {==}
    case Con{Lex.Tok{+k, +t, +l, +c}, +rest}:
      +more = Prefix.walk(rest, path)
      +m = Laws.prefix_count(rest)
      %prefix.at(k, t, rest) : {List.length(&2, F.Finding, Prefix.hit(Prefix.at(k, t, rest), path, l, c, more))
        == Bool.pick(Nat, _, 1n+m, m) : Nat}
      prefix.hit(Prefix.at(k, t, rest), path, l, c, more, m, prefix.walk(rest, path))

def Laws.prefix_counts(path, _text, toks, _tree, _bound, _items):
  M1.put.stop(Paths.is_law_file(path), Prefix.walk(T.sig(toks), path), Laws.prefix_count(T.sig(toks)),
    prefix.walk(T.sig(toks), path))
