# proofs of laws/InertEmpty.bend
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/rules/tokens.bend as T
import ../src/paths.bend as Paths
import ../src/lazy/lazy.bend as Lazy
import ../src/rules/suspicious/empty.bend as Empty
import ../laws/InertEmpty.bend as Laws
import ../laws/defs/InertText.bend as D1
import ./lemmas/InertTextFacts.bend as M1

# a found name with the tokens after it read that way
def inert.empty.taken(m: Maybe<&2, Empty.Taken>) -> Maybe<&2, Empty.Taken>:
  match m:
    case None{}:
      None{}
    case Some{Empty.Taken{x, r}}:
      Some{Empty.Taken{x, D1.inert.toks(r)}}

# a token's text read that way is the same code: a comment or a string is
# none either way, anything else is kept as it is
law inert.empty.code:
  for k: Lex.TokKind
  for +t: String
  {Empty.code(k, D1.inert.keep(D1.inert.blanks(k), t)) == Empty.code(k, t) : String}

def inert.empty.code(k, _t):
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

# the last tokens of a length's arguments are what they were
law inert.empty.last:
  for k: Lex.TokKind
  for +t: String
  for +l: Empty.Last
  {Empty.last.step(k, D1.inert.keep(D1.inert.blanks(k), t), l) == Empty.last.step(k, t, l) : Empty.Last}

def inert.empty.last(k, _t, _ll):
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

# the name a length's arguments end in, before tokens read that way
law inert.empty.name:
  for +l: Empty.Last
  for r: List<&2, Lex.Tok>
  {Empty.last.name(l, D1.inert.toks(r)) == inert.empty.taken(Empty.last.name(l, r)) : Maybe<&2, Empty.Taken>}

def inert.empty.name(l, _r):
  match l:
    case Empty.LComma{}:
      {==}
    case Empty.LName{_n}:
      {==}
    case Empty.LOther{}:
      {==}

# a pick of that name, or none
law inert.empty.name_pick:
  for h: Bool
  for +l: Empty.Last
  for r: List<&2, Lex.Tok>
  {Bool.pick(Maybe<&2, Empty.Taken>, h, Empty.last.name(l, D1.inert.toks(r)), None{})
    == inert.empty.taken(Bool.pick(Maybe<&2, Empty.Taken>, h, Empty.last.name(l, r), None{})) : Maybe<&2, Empty.Taken>}

def inert.empty.name_pick(h, l, r):
  match h:
    case True{}:
      inert.empty.name(l, r)
    case False{}:
      {==}

# whether x is kept does not read what a comment or string says
law inert.empty.kept:
  for ts: List<&2, Lex.Tok>
  for +x: String
  for +d: Nat
  for found: Bool
  for live: Bool
  {Empty.kept(D1.inert.toks(ts), x, d, found, live) == Empty.kept(ts, x, d, found, live) : Bool}

def inert.empty.kept(ts, x, d, found, live):
  match ts:
    case Nil{}:
      {==}
    case Con{Lex.Tok{+k, +t, +l, +c}, +rest}:
      match found:
        case True{}:
          {==}
        case False{}:
          match live:
            case False{}:
              {==}
            case True{}:
              +dep = Empty.close.depth(k, d)
              +nh = Bool.not(Empty.close.here(k, d))
              +ck = Empty.code(k, D1.inert.keep(D1.inert.blanks(k), t))
              %inert.empty.code(k, t) : {Empty.kept(D1.inert.toks(rest), x, dep, Bool.and(Empty.plain(k),
                String.eq(ck, x)), nh)
                == Empty.kept(rest, x, dep, Bool.and(Empty.plain(k), String.eq(_, x)), nh) : Bool}
              inert.empty.kept(rest, x, dep, Bool.and(Empty.plain(k), String.eq(ck, x)), nh)

# a List.length's arguments end in the same name, the tokens after it read
# that way
law inert.empty.list:
  for ts: List<&2, Lex.Tok>
  for +d: Nat
  for +l: Empty.Last
  for done: Bool
  for got: Maybe<&2, Empty.Taken>
  {Empty.close.list(D1.inert.toks(ts), d, l, done, inert.empty.taken(got))
    == inert.empty.taken(Empty.close.list(ts, d, l, done, got)) : Maybe<&2, Empty.Taken>}

def inert.empty.list(ts, d, ll, done, _got):
  match ts:
    case Nil{}:
      {==}
    case Con{Lex.Tok{+k, +t, +l, +c}, +rest}:
      match done:
        case True{}:
          {==}
        case False{}:
          +dep = Empty.close.depth(k, d)
          +h = Empty.close.here(k, d)
          +lk = Empty.last.step(k, D1.inert.keep(D1.inert.blanks(k), t), ll)
          +ls = Empty.last.step(k, t, ll)
          +pk = Bool.pick(Maybe<&2, Empty.Taken>, h, Empty.last.name(ll, D1.inert.toks(rest)), None{})
          +ps = Bool.pick(Maybe<&2, Empty.Taken>, h, Empty.last.name(ll, rest), None{})
          +rhs = inert.empty.taken(Empty.close.list(rest, dep, ls, h, ps))
          %Equal.sym(Empty.Last, lk, ls, inert.empty.last(k, t, ll)) :
            {Empty.close.list(D1.inert.toks(rest), dep, _, h, pk) == rhs : Maybe<&2, Empty.Taken>}
          %Equal.sym(Maybe<&2, Empty.Taken>, pk, inert.empty.taken(ps), inert.empty.name_pick(h, ll, rest)) :
            {Empty.close.list(D1.inert.toks(rest), dep, ls, h, _) == rhs : Maybe<&2, Empty.Taken>}
          inert.empty.list(rest, dep, ls, h, ps)

# a pick of a found name, the tokens after it read that way
law inert.empty.found:
  for b: Bool
  for +y: String
  for r: List<&2, Lex.Tok>
  {Bool.pick(Maybe<&2, Empty.Taken>, b, Some{Empty.Taken{y, D1.inert.toks(r)}}, None{})
    == inert.empty.taken(Bool.pick(Maybe<&2, Empty.Taken>, b, Some{Empty.Taken{y, r}},
      None{})) : Maybe<&2, Empty.Taken>}

def inert.empty.found(b, _y, _r):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# a String.length's argument is the same name, the tokens after it read
# that way
law inert.empty.str:
  for ts: List<&2, Lex.Tok>
  {Empty.close.str(D1.inert.toks(ts)) == inert.empty.taken(Empty.close.str(ts)) : Maybe<&2, Empty.Taken>}

def inert.empty.str(ts):
  match ts:
    case Nil{}:
      {==}
    case Con{Lex.Tok{+k1, +t1, +l1, +c1}, +r1}:
      match r1:
        case Nil{}:
          {==}
        case Con{Lex.Tok{+k2, +t2, +l2, +c2}, +rest}:
          +c1k = Empty.code(k1, D1.inert.keep(D1.inert.blanks(k1), t1))
          +c2k = Empty.code(k2, D1.inert.keep(D1.inert.blanks(k2), t2))
          +rhs = inert.empty.taken(Bool.pick(Maybe<&2, Empty.Taken>, Bool.and(Empty.plain(k1),
            String.eq(Empty.code(k2, t2), ")")),
            Some{Empty.Taken{Empty.code(k1, t1), rest}}, None{}))
          %Equal.sym(String, c1k, Empty.code(k1, t1), inert.empty.code(k1, t1)) :
            {Bool.pick(Maybe<&2, Empty.Taken>, Bool.and(Empty.plain(k1), String.eq(c2k, ")")),
              Some{Empty.Taken{_, D1.inert.toks(rest)}}, None{}) == rhs : Maybe<&2, Empty.Taken>}
          %Equal.sym(String, c2k, Empty.code(k2, t2), inert.empty.code(k2, t2)) :
            {Bool.pick(Maybe<&2, Empty.Taken>, Bool.and(Empty.plain(k1), String.eq(_, ")")),
              Some{Empty.Taken{Empty.code(k1, t1), D1.inert.toks(rest)}}, None{}) == rhs : Maybe<&2, Empty.Taken>}
          inert.empty.found(Bool.and(Empty.plain(k1), String.eq(Empty.code(k2, t2), ")")), Empty.code(k1, t1), rest)

# a length's argument is the same name, the tokens after it read that way
law inert.empty.taken_of:
  for +fm: Empty.Form
  for ts: List<&2, Lex.Tok>
  {Empty.taken(fm, D1.inert.toks(ts)) == inert.empty.taken(Empty.taken(fm, ts)) : Maybe<&2, Empty.Taken>}

def inert.empty.taken_of(fm, ts):
  match fm:
    case Empty.FList{}:
      inert.empty.list(ts, 0n, Empty.LOther{}, False{}, None{})
    case Empty.FStr{}:
      inert.empty.str(ts)
    case Empty.FNone{}:
      {==}

# the test's end and the read of x after it give the same finding
law inert.empty.tail:
  for m: Maybe<&2, Empty.Taken>
  for +fm: Empty.Form
  for +l: U32
  for +c: U32
  {Empty.tail(inert.empty.taken(m), fm, l, c) == Empty.tail(m, fm, l, c) : Maybe<&2, Empty.Hit>}

def inert.empty.tail(m, fm, l, c):
  match m:
    case None{}:
      {==}
    case Some{Empty.Taken{+x, +r}}:
      match r:
        case Nil{}:
          {==}
        case Con{Lex.Tok{+k1, +t1, +l1, +c1}, +r1}:
          match r1:
            case Nil{}:
              {==}
            case Con{Lex.Tok{+k2, +t2, +l2, +c2}, +r2}:
              match r2:
                case Nil{}:
                  {==}
                case Con{Lex.Tok{+k3, +t3, +l3, +c3}, +rest}:
                  +s1 = Empty.code(k1, t1)
                  +s2 = Empty.code(k2, t2)
                  +s3 = Empty.code(k3, t3)
                  +rhs = Empty.tail.go(Bool.and(String.eq(s1, ","), Bool.and(String.eq(s2, "0n"), Bool.and(String.eq(s3,
                    ")"),
                    Empty.kept(rest, x, 0n, False{}, True{})))), fm, x, l, c)
                  %Equal.sym(String, Empty.code(k1, D1.inert.keep(D1.inert.blanks(k1), t1)), s1, inert.empty.code(k1,
                    t1)) :
                    {Empty.tail.go(Bool.and(String.eq(_, ","), Bool.and(String.eq(Empty.code(k2,
                      D1.inert.keep(D1.inert.blanks(k2), t2)), "0n"),
                      Bool.and(String.eq(Empty.code(k3, D1.inert.keep(D1.inert.blanks(k3), t3)), ")"),
                      Empty.kept(D1.inert.toks(rest), x, 0n, False{},
                        True{})))), fm, x, l, c) == rhs : Maybe<&2, Empty.Hit>}
                  %Equal.sym(String, Empty.code(k2, D1.inert.keep(D1.inert.blanks(k2), t2)), s2, inert.empty.code(k2,
                    t2)) :
                    {Empty.tail.go(Bool.and(String.eq(s1, ","), Bool.and(String.eq(_, "0n"),
                      Bool.and(String.eq(Empty.code(k3, D1.inert.keep(D1.inert.blanks(k3), t3)), ")"),
                      Empty.kept(D1.inert.toks(rest), x, 0n, False{},
                        True{})))), fm, x, l, c) == rhs : Maybe<&2, Empty.Hit>}
                  %Equal.sym(String, Empty.code(k3, D1.inert.keep(D1.inert.blanks(k3), t3)), s3, inert.empty.code(k3,
                    t3)) :
                    {Empty.tail.go(Bool.and(String.eq(s1, ","), Bool.and(String.eq(s2, "0n"), Bool.and(String.eq(_, ")"),
                      Empty.kept(D1.inert.toks(rest), x, 0n, False{},
                        True{})))), fm, x, l, c) == rhs : Maybe<&2, Empty.Hit>}
                  %Equal.sym(Bool, Empty.kept(D1.inert.toks(rest), x, 0n, False{}, True{}), Empty.kept(rest, x, 0n,
                    False{}, True{}),
                    inert.empty.kept(rest, x, 0n, False{}, True{})) :
                    {Empty.tail.go(Bool.and(String.eq(s1, ","), Bool.and(String.eq(s2, "0n"), Bool.and(String.eq(s3, ")"),
                      _))),
                      fm, x, l, c) == rhs : Maybe<&2, Empty.Hit>}
                  {==}

# the test, its head read, gives the same finding
law inert.empty.at_go:
  for ok: Bool
  for +fm: Empty.Form
  for +l: U32
  for +c: U32
  for +r: List<&2, Lex.Tok>
  {Empty.at.go(ok, fm, l, c, D1.inert.toks(r)) == Empty.at.go(ok, fm, l, c, r) : Maybe<&2, Empty.Hit>}

def inert.empty.at_go(ok, fm, l, c, r):
  match ok:
    case True{}:
      %Equal.sym(Maybe<&2, Empty.Taken>, Empty.taken(fm, D1.inert.toks(r)), inert.empty.taken(Empty.taken(fm, r)),
        inert.empty.taken_of(fm, r)) :
        {Empty.tail(_, fm, l, c) == Empty.tail(Empty.taken(fm, r), fm, l, c) : Maybe<&2, Empty.Hit>}
      inert.empty.tail(Empty.taken(fm, r), fm, l, c)
    case False{}:
      {==}

# a token's kind, then tokens read that way: the same kept test, if any
law inert.empty.at:
  for k0: Lex.TokKind
  for ts: List<&2, Lex.Tok>
  {Empty.at(k0, D1.inert.toks(ts)) == Empty.at(k0, ts) : Maybe<&2, Empty.Hit>}

def inert.empty.at(k0, ts):
  match ts:
    case Nil{}:
      {==}
    case Con{Lex.Tok{+k1, +t1, +l1, +c1}, +r1}:
      match r1:
        case Nil{}:
          {==}
        case Con{Lex.Tok{+k2, +t2, +l2, +c2}, +r2}:
          match r2:
            case Nil{}:
              {==}
            case Con{Lex.Tok{+k3, +t3, +l3, +c3}, +r3}:
              match r3:
                case Nil{}:
                  {==}
                case Con{Lex.Tok{+k4, +t4, +l4, +c4}, +r4}:
                  +q1 = Empty.code(k1, D1.inert.keep(D1.inert.blanks(k1), t1))
                  +q2 = Empty.code(k2, D1.inert.keep(D1.inert.blanks(k2), t2))
                  +q3 = Empty.code(k3, D1.inert.keep(D1.inert.blanks(k3), t3))
                  +q4 = Empty.code(k4, D1.inert.keep(D1.inert.blanks(k4), t4))
                  +ok = Bool.and(Empty.opener(k0), Bool.and(Empty.dotted(k1), Bool.and(Empty.dotted(k3),
                    Bool.and(String.eq(q1, "Nat.is_eq"), Bool.and(String.eq(q2, "("), String.eq(q4, "("))))))
                  +lhs = Empty.at.go(ok, Empty.form(q3), l1, c1, D1.inert.toks(r4))
                  %inert.empty.code(k1, t1) : {lhs == Empty.at.go(Bool.and(Empty.opener(k0), Bool.and(Empty.dotted(k1),
                    Bool.and(Empty.dotted(k3), Bool.and(String.eq(_, "Nat.is_eq"), Bool.and(String.eq(Empty.code(k2, t2), "("),
                    String.eq(Empty.code(k4, t4),
                      "(")))))), Empty.form(Empty.code(k3, t3)), l1, c1, r4) : Maybe<&2, Empty.Hit>}
                  %inert.empty.code(k2, t2) : {lhs == Empty.at.go(Bool.and(Empty.opener(k0), Bool.and(Empty.dotted(k1),
                    Bool.and(Empty.dotted(k3), Bool.and(String.eq(q1, "Nat.is_eq"), Bool.and(String.eq(_, "("),
                    String.eq(Empty.code(k4, t4),
                      "(")))))), Empty.form(Empty.code(k3, t3)), l1, c1, r4) : Maybe<&2, Empty.Hit>}
                  %inert.empty.code(k4, t4) : {lhs == Empty.at.go(Bool.and(Empty.opener(k0), Bool.and(Empty.dotted(k1),
                    Bool.and(Empty.dotted(k3), Bool.and(String.eq(q1, "Nat.is_eq"), Bool.and(String.eq(q2, "("),
                    String.eq(_, "(")))))), Empty.form(Empty.code(k3, t3)), l1, c1, r4) : Maybe<&2, Empty.Hit>}
                  %inert.empty.code(k3, t3) : {lhs == Empty.at.go(ok, Empty.form(_), l1, c1, r4) : Maybe<&2, Empty.Hit>}
                  inert.empty.at_go(ok, Empty.form(q3), l1, c1, r4)

# what follows a def's parameters says the same
law inert.empty.head:
  for k1: Lex.TokKind
  for +k2: Lex.TokKind
  for +t2: String
  {Empty.proofy.head(k1, k2, D1.inert.keep(D1.inert.blanks(k2), t2)) == Empty.proofy.head(k1, k2, t2) : Bool}

def inert.empty.head(k1, k2, t2):
  match k1:
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
      %inert.empty.code(k2, t2) : {String.eq(Empty.code(k2, D1.inert.keep(D1.inert.blanks(k2), t2)),
        "{") == String.eq(_, "{") : Bool}
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

# a def's header ends the same way
law inert.empty.end:
  for ts: List<&2, Lex.Tok>
  {Empty.proofy.end(D1.inert.toks(ts)) == Empty.proofy.end(ts) : Bool}

def inert.empty.end(ts):
  match ts:
    case Nil{}:
      {==}
    case Con{Lex.Tok{+k1, +t1, +l1, +c1}, +r1}:
      match r1:
        case Nil{}:
          {==}
        case Con{Lex.Tok{+k2, +t2, +l2, +c2}, +rest}:
          inert.empty.head(k1, k2, t2)

# a def is a proof or not the same way
law inert.empty.proofy:
  for ts: List<&2, Lex.Tok>
  for +d: Nat
  for fin: Bool
  {Empty.proofy(D1.inert.toks(ts), d, fin) == Empty.proofy(ts, d, fin) : Bool}

def inert.empty.proofy(ts, d, fin):
  match ts:
    case Nil{}:
      {==}
    case Con{Lex.Tok{+k, +t, +l, +c}, +rest}:
      match fin:
        case True{}:
          inert.empty.end(Lex.Tok{k, t, l, c} <> rest)
        case False{}:
          inert.empty.proofy(rest, Empty.close.depth(k, d), Empty.proofy.fin(k, d))

# what a keyword leaves skipped is the same
law inert.empty.word:
  for isdef: Bool
  for +word: String
  for rest: List<&2, Lex.Tok>
  for skip: Bool
  {Empty.item.word(isdef, word, D1.inert.toks(rest), skip) == Empty.item.word(isdef, word, rest, skip) : Bool}

def inert.empty.word(isdef, _word, rest, _skip):
  match isdef:
    case True{}:
      inert.empty.proofy(rest, 0n, False{})
    case False{}:
      {==}

# what a token leaves skipped is the same
law inert.empty.item:
  for k: Lex.TokKind
  for +t: String
  for rest: List<&2, Lex.Tok>
  for skip: Bool
  {Empty.item(k, D1.inert.keep(D1.inert.blanks(k), t), D1.inert.toks(rest), skip) == Empty.item(k, t, rest,
    skip) : Bool}

def inert.empty.item(k, t, rest, skip):
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
      inert.empty.word(String.eq(t, "def"), t, rest, skip)
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

# the test a token opens, outside what is skipped, is the same
law inert.empty.opens:
  for sk: Bool
  for k: Lex.TokKind
  for rest: List<&2, Lex.Tok>
  {Empty.found(sk, k, D1.inert.toks(rest)) == Empty.found(sk, k, rest) : Maybe<&2, Empty.Hit>}

def inert.empty.opens(sk, k, rest):
  match sk:
    case True{}:
      {==}
    case False{}:
      inert.empty.at(k, rest)

# the walk finds the same tests in tokens read that way
law inert.empty.walk:
  for ts: List<&2, Lex.Tok>
  for +path: String
  for +skip: Bool
  {Empty.walk(D1.inert.toks(ts), path, skip) == Empty.walk(ts, path, skip) : List<&2, F.Finding>}

def inert.empty.walk(ts, path, skip):
  match ts:
    case Nil{}:
      {==}
    case Con{Lex.Tok{+k, +t, +l, +c}, +rest}:
      +sk = Empty.item(k, t, rest, skip)
      %Equal.sym(Bool, Empty.item(k, D1.inert.keep(D1.inert.blanks(k), t), D1.inert.toks(rest), skip), sk,
        inert.empty.item(k, t, rest, skip)) :
        {Empty.hit(Empty.found(_, k, D1.inert.toks(rest)), path, Empty.walk(D1.inert.toks(rest), path, _))
          == Empty.hit(Empty.found(sk, k, rest), path, Empty.walk(rest, path, sk)) : List<&2, F.Finding>}
      %Equal.sym(Maybe<&2, Empty.Hit>, Empty.found(sk, k, D1.inert.toks(rest)), Empty.found(sk, k, rest),
        inert.empty.opens(sk, k, rest)) :
        {Empty.hit(_, path, Empty.walk(D1.inert.toks(rest), path, sk))
          == Empty.hit(Empty.found(sk, k, rest), path, Empty.walk(rest, path, sk)) : List<&2, F.Finding>}
      %Equal.sym(List<&2, F.Finding>, Empty.walk(D1.inert.toks(rest), path, sk), Empty.walk(rest, path, sk),
        inert.empty.walk(rest, path, sk)) :
        {Empty.hit(Empty.found(sk, k, rest), path, _) == Empty.hit(Empty.found(sk, k, rest), path, Empty.walk(rest,
          path, sk))
          : List<&2, F.Finding>}
      {==}

# the walk of the significant tokens reads no comment or string
law inert.empty.on:
  for +ts: List<&2, Lex.Tok>
  for +path: String
  {Empty.walk(T.sig(D1.inert.toks(ts)), path, False{}) == Empty.walk(T.sig(ts), path, False{}) : List<&2, F.Finding>}

def inert.empty.on(ts, path):
  +s = T.sig(ts)
  %Equal.sym(List<&2, Lex.Tok>, T.sig(D1.inert.toks(ts)), D1.inert.toks(s), M1.inert.put.sig(ts)) :
    {Empty.walk(_, path, False{}) == Empty.walk(s, path, False{}) : List<&2, F.Finding>}
  inert.empty.walk(s, path, False{})

def Laws.inert_empty(path, _text, toks, _tree, _bound, _items, _text2, toks2, _tree2, _bound2, _items2, e):
  M1.inert.via(List<&2, Lex.Tok>, z => Lazy.stop(List<&2, F.Finding>, Paths.is_law_file(path), [],
    _u => Empty.walk(T.sig(z), path, False{})), toks, toks2, D1.inert.toks(toks), D1.inert.toks(toks2),
    Equal.cong(List<&2, F.Finding>, List<&2, F.Finding>, w => Lazy.stop(List<&2, F.Finding>, Paths.is_law_file(path),
      [], _u => w), Empty.walk(T.sig(D1.inert.toks(toks)), path, False{}), Empty.walk(T.sig(toks), path, False{}),
      inert.empty.on(toks, path)),
    Equal.cong(List<&2, F.Finding>, List<&2, F.Finding>, w => Lazy.stop(List<&2, F.Finding>, Paths.is_law_file(path),
      [], _u => w), Empty.walk(T.sig(D1.inert.toks(toks2)), path, False{}), Empty.walk(T.sig(toks2), path, False{}),
      inert.empty.on(toks2, path)),
    e)
