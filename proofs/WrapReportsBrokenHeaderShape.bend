# proofs of laws/WrapReportsBrokenHeaderShape.bend
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/lazy/lazy.bend as Lazy
import ../src/rules/correctness/put.bend as Put
import ../src/syntax/outline.bend as Outline
import ../src/rules/style/wrap.bend as Wrap
import ../laws/WrapReportsBrokenHeaderShape.bend as Laws
import ./lemmas/Put.bend as M1

# The header rule wrap (laws/WrapReportsBrokenHeaderShape.bend). The width walk agrees with the
# spec's width from any state; the shape walk, read through wrap.of, takes
# each token the way the spec's read does, so the two agree on the whole
# header; the verdicts agree on what they read.

# a token's share of the width is the spec's
law wrap.cost:
  for k: Lex.TokKind
  for +tx: String
  {Wrap.check.cost(k, tx) == Laws.wrap.cost(k, tx) : U32}

def wrap.cost(k, _tx):
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

# a colon or not, and a colon or not later on: the walk from here is the spec's
law wrap.width_step:
  for c: Bool
  for h: Bool
  for +next: U32
  for +upto: U32
  for +seen: Bool
  for -u: U32
  for -t: U32
  for -x: U32
  for ih: {x == Bool.pick(U32, h, u, Bool.pick(U32, Bool.or(c, seen), Bool.pick(U32, c, next, upto), t)) : U32}
  {x == Bool.pick(U32, Bool.or(c, h), Bool.pick(U32, h, u, next), Bool.pick(U32, seen, upto, t)) : U32}

def wrap.width_step(c, h, _next, _upto, _seen, _uu, _tt, _x, ih):
  match c:
    case True{}:
      ih
    case False{}:
      match h:
        case True{}:
          ih
        case False{}:
          ih

# the width walk from any state: through the last `:` when the rest has one,
# else the `:` already seen, else the whole width
law wrap.width_go:
  for +toks: List<&2, Lex.Tok>
  for +acc: U32
  for +upto: U32
  for +seen: Bool
  {Wrap.check.width.go(toks, acc, upto, seen)
    == Bool.pick(U32, Laws.wrap.colons(toks), Laws.wrap.upto(toks, acc),
      Bool.pick(U32, seen, upto, Laws.wrap.total(toks, acc))) : U32}

def wrap.width_go(toks, acc, upto, seen):
  match toks:
    case Nil{}:
      {==}
    case Con{Lex.Tok{+k, +tx, _ln, _cl}, +rest}:
      +next = (acc + Wrap.check.cost(k, tx) : U32)
      +colon = Wrap.check.is_colon(k)
      +h = Laws.wrap.colons(rest)
      %wrap.cost(k, tx) : {Wrap.check.width.go(rest, next, Bool.pick(U32, colon, next, upto), Bool.or(colon, seen))
        == Bool.pick(U32, Bool.or(colon, h), Bool.pick(U32, h, Laws.wrap.upto(rest, (acc + _ : U32)), (acc + _ : U32)),
          Bool.pick(U32, seen, upto, Laws.wrap.total(rest, (acc + _ : U32)))) : U32}
      wrap.width_step(colon, h, next, upto, seen, Laws.wrap.upto(rest, next),
        Laws.wrap.total(rest, next),
        Wrap.check.width.go(rest, next, Bool.pick(U32, colon, next, upto), Bool.or(colon, seen)),
        wrap.width_go(rest, next, Bool.pick(U32, colon, next, upto), Bool.or(colon, seen)))

def Laws.wrap_width(toks):
  wrap.width_go(toks, 0, 0, False{})

# the `)`'s line
def wrap.line_of(sp: Wrap.Span) -> U32:
  Wrap.Span{line, _end, _col} = sp
  line

# the parameter being read, when one is
def wrap.cur_of(on: Bool, +pline: U32, +pend: U32, +pcol: U32) -> Maybe<&2, Wrap.Span>:
  Bool.pick(Maybe<&2, Wrap.Span>, on, Some{Wrap.Span{pline, pend, pcol}}, None{})

# the rule's walk as the spec's read
def wrap.of(wk: Wrap.Walk) -> Laws.wrap.Read:
  Wrap.Walk{mode, paren, bracket, brace, angle, shut, open, on, pline, pend, pcol, spans} = wk
  Laws.wrap.Read{mode, paren, bracket, brace, angle, open, wrap.line_of(shut), wrap.cur_of(on, pline, pend, pcol),
    spans}

# before the list: the rule's seek is the spec's
law wrap.seek_open:
  for a: Bool
  for z: Bool
  for +r: Wrap.Act
  {Bool.pick(Wrap.Act, Bool.and(a, z), Wrap.AOpen{}, r) == Wrap.check.seek_open(a, z, r) : Wrap.Act}

def wrap.seek_open(a, z, _r):
  match a:
    case True{}:
      match z:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      {==}

# inside the list: the rule's edges are the spec's
law wrap.args_end:
  for c: Bool
  for +t: Bool
  for m: Bool
  for +r: Wrap.Act
  {Bool.pick(Wrap.Act, t, Bool.pick(Wrap.Act, c, Wrap.AEnd{}, Bool.pick(Wrap.Act, m, Wrap.AComma{}, r)), r)
    == Wrap.check.args_end(c, t, Wrap.check.args_comma(m, t, r)) : Wrap.Act}

def wrap.args_end(c, t, m, _r):
  match c:
    case True{}:
      match t:
        case True{}:
          {==}
        case False{}:
          match m:
            case True{}:
              {==}
            case False{}:
              {==}
    case False{}:
      match t:
        case True{}:
          match m:
            case True{}:
              {==}
            case False{}:
              {==}
        case False{}:
          match m:
            case True{}:
              {==}
            case False{}:
              {==}

# the spec's motion of a token is the rule's
law wrap.motion:
  for at: Wrap.Phase
  for +k: Lex.TokKind
  for +tx: String
  for +glued: Bool
  for +paren: U32
  for +bracket: U32
  for +brace: U32
  for +angle: U32
  {Laws.wrap.motion(at, k, tx, glued, paren, bracket, brace, angle)
    == Wrap.check.act(at, k, tx, glued, paren, angle, brace, bracket) : Wrap.Act}

def wrap.motion(at, k, tx, glued, paren, bracket, brace, angle):
  match at:
    case Wrap.Seek{}:
      wrap.seek_open(Wrap.check.is_oparen(k, tx), Wrap.check.zero(paren, angle, brace, bracket),
        Wrap.check.brackets(k, tx, glued))
    case Wrap.Args{}:
      wrap.args_end(Wrap.check.is_cparen(k, tx), Wrap.check.top(paren, angle, brace, bracket), Lex.is_comma(k),
        Wrap.check.brackets(k, tx, glued))
    case Wrap.Past{}:
      {==}
    case Wrap.Shut{}:
      {==}
    case Wrap.Loose{}:
      {==}

# a pick and an early exit that agree on both branches agree
law wrap.stop_pick:
  for c: Bool
  for +a: U32
  for -x: U32
  for -y: U32
  for e: {x == y : U32}
  {Bool.pick(U32, c, a, x) == Lazy.stop(U32, c, a, _u => y) : U32}

def wrap.stop_pick(c, _a, _x, _y, e):
  match c:
    case True{}:
      {==}
    case False{}:
      e

# the spec closes angles as the rule does
law wrap.lower:
  for n: Nat
  for +angle: U32
  {Laws.wrap.lower(n, angle) == Wrap.check.sub(n, angle) : U32}

def wrap.lower(n, angle):
  match n:
    case Zero{}:
      {==}
    case Succ{p}:
      wrap.stop_pick(U32.is_eq(angle, 0), angle, Laws.wrap.lower(p, (angle - 1 : U32)),
        Wrap.check.sub(p, (angle - 1 : U32)), wrap.lower(p, (angle - 1 : U32)))

# a token that moves only the depths: inside the list it joins the parameter
law wrap.joined:
  for mode: Wrap.Phase
  for on: Bool
  for +paren: U32
  for +bracket: U32
  for +brace: U32
  for +angle: U32
  for +shut: Wrap.Span
  for +open: U32
  for +pline: U32
  for +pend: U32
  for +pcol: U32
  for +spans: List<&2, Wrap.Span>
  for +k: Lex.TokKind
  for +tx: String
  for +ln: U32
  for +cl: U32
  {wrap.of(Wrap.check.note_args(Wrap.Walk{mode, paren, bracket, brace, angle, shut, open, on, pline, pend, pcol, spans},
    Lex.Tok{k, tx, ln, cl}))
    == Laws.wrap.join(mode, paren, bracket, brace, angle, open, wrap.line_of(shut), wrap.cur_of(on, pline, pend, pcol),
      spans, ln, cl) : Laws.wrap.Read}

def wrap.joined(
  mode,
  on,
  _paren,
  _bracket,
  _brace,
  _angle,
  _shut,
  _open,
  _pline,
  _pend,
  _pcol,
  _spans,
  _kk,
  _tx,
  _ln,
  _cl
):
  match mode:
    case Wrap.Args{}:
      match on:
        case True{}:
          {==}
        case False{}:
          {==}
    case Wrap.Seek{}:
      {==}
    case Wrap.Past{}:
      {==}
    case Wrap.Shut{}:
      {==}
    case Wrap.Loose{}:
      {==}

# a `->` right after the `)`: past it, on the `)` line or not, nothing joins
law wrap.arrowed:
  for b: Bool
  for on: Bool
  for +paren: U32
  for +bracket: U32
  for +brace: U32
  for +angle: U32
  for +shut: Wrap.Span
  for +open: U32
  for +pline: U32
  for +pend: U32
  for +pcol: U32
  for +spans: List<&2, Wrap.Span>
  for +tok: Lex.Tok
  {wrap.of(Wrap.check.note_args(Wrap.Walk{Bool.pick(Wrap.Phase, b, Wrap.Past{}, Wrap.Loose{}), paren, bracket, brace,
    angle, shut, open, on, pline, pend, pcol, spans}, tok))
    == Laws.wrap.Read{Bool.pick(Wrap.Phase, b, Wrap.Past{}, Wrap.Loose{}), paren, bracket, brace, angle, open,
      wrap.line_of(shut), wrap.cur_of(on, pline, pend, pcol), spans} : Laws.wrap.Read}

def wrap.arrowed(b, _on, _paren, _bracket, _brace, _angle, _shut, _open, _pline, _pend, _pcol, _spans, _tok):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# any motion: the rule's walk after it is the spec's read after it
law wrap.moved:
  for m: Wrap.Act
  for mode: Wrap.Phase
  for on: Bool
  for +paren: U32
  for +bracket: U32
  for +brace: U32
  for +angle: U32
  for +shut: Wrap.Span
  for +open: U32
  for +pline: U32
  for +pend: U32
  for +pcol: U32
  for +spans: List<&2, Wrap.Span>
  for +k: Lex.TokKind
  for +tx: String
  for +ln: U32
  for +cl: U32
  for +ticks: Nat
  {wrap.of(Wrap.check.maybe_note(Wrap.check.is_sep(m),
    Wrap.check.apply(m, Wrap.Walk{mode, paren, bracket, brace, angle, shut, open, on, pline, pend, pcol, spans}, ln, cl,
      ticks), Lex.Tok{k, tx, ln, cl}))
    == Laws.wrap.move(m, mode, paren, bracket, brace, angle, open, wrap.line_of(shut),
      wrap.cur_of(on, pline, pend, pcol), spans, ln, cl, ticks) : Laws.wrap.Read}

def wrap.moved(m, mode, on, paren, bracket, brace, angle, shut, open, pline, pend, pcol, spans, k, tx, ln, cl, ticks):
  match m:
    case Wrap.AOpen{}:
      {==}
    case Wrap.AEnd{}:
      match on:
        case True{}:
          {==}
        case False{}:
          {==}
    case Wrap.AComma{}:
      match on:
        case True{}:
          {==}
        case False{}:
          {==}
    case Wrap.AArrow{}:
      match shut:
        case Wrap.Span{+line, +end, +col}:
          wrap.arrowed(U32.is_eq(ln, line), on, paren, bracket, brace, angle, Wrap.Span{line, end, col}, open, pline,
            pend, pcol, spans, Lex.Tok{k, tx, ln, cl})
    case Wrap.AStray{}:
      {==}
    case Wrap.AParen{}:
      wrap.joined(mode, on, (paren + 1 : U32), bracket, brace, angle, shut,
        open, pline, pend, pcol, spans, k, tx, ln, cl)
    case Wrap.AUnparen{}:
      wrap.joined(mode, on, Wrap.check.dec_u(paren), bracket, brace, angle, shut,
        open, pline, pend, pcol, spans, k, tx, ln, cl)
    case Wrap.ABrack{}:
      wrap.joined(mode, on, paren, (bracket + 1 : U32), brace, angle, shut,
        open, pline, pend, pcol, spans, k, tx, ln, cl)
    case Wrap.AUnbrack{}:
      wrap.joined(mode, on, paren, Wrap.check.dec_u(bracket), brace, angle, shut,
        open, pline, pend, pcol, spans, k, tx, ln, cl)
    case Wrap.ABrace{}:
      wrap.joined(mode, on, paren, bracket, (brace + 1 : U32), angle, shut,
        open, pline, pend, pcol, spans, k, tx, ln, cl)
    case Wrap.AUnbrace{}:
      wrap.joined(mode, on, paren, bracket, Wrap.check.dec_u(brace), angle, shut,
        open, pline, pend, pcol, spans, k, tx, ln, cl)
    case Wrap.AAngle{}:
      wrap.joined(mode, on, paren, bracket, brace, (angle + 1 : U32), shut,
        open, pline, pend, pcol, spans, k, tx, ln, cl)
    case Wrap.AUnangle{}:
      %wrap.lower(ticks, angle) : {wrap.of(Wrap.check.note_args(Wrap.Walk{mode, paren, bracket, brace, _, shut, open,
        on, pline, pend, pcol, spans}, Lex.Tok{k, tx, ln, cl})) == Laws.wrap.join(mode, paren, bracket, brace,
        Laws.wrap.lower(ticks, angle), open, wrap.line_of(shut), wrap.cur_of(on, pline, pend, pcol), spans, ln, cl)
        : Laws.wrap.Read}
      wrap.joined(mode, on, paren, bracket, brace, Laws.wrap.lower(ticks, angle), shut,
        open, pline, pend, pcol, spans, k, tx, ln, cl)
    case Wrap.ANone{}:
      wrap.joined(mode, on, paren, bracket, brace, angle, shut,
        open, pline, pend, pcol, spans, k, tx, ln, cl)

# a significant token or not: the rule's step and the spec's agree when they
# agree on a significant one
law wrap.on_sig:
  for s: Bool
  for +tok: Lex.Tok
  for +wk: Wrap.Walk
  for +glued: Bool
  for -y: Laws.wrap.Read
  for e: {wrap.of(Wrap.check.step_hit(wk, tok, glued)) == y : Laws.wrap.Read}
  {wrap.of(Wrap.check.step_on(s, tok, wk, glued)) == Bool.pick(Laws.wrap.Read, s, y, wrap.of(wk)) : Laws.wrap.Read}

def wrap.on_sig(s, _tok, _wk, _glued, _y, e):
  match s:
    case True{}:
      e
    case False{}:
      {==}

# one token: the rule's walk after it is the spec's read after it
law wrap.stepped:
  for +tok: Lex.Tok
  for +wk: Wrap.Walk
  for +glued: Bool
  {wrap.of(Wrap.check.step(tok, wk, glued)) == Laws.wrap.step(tok, wrap.of(wk), glued) : Laws.wrap.Read}

def wrap.stepped(tok, wk, glued):
  match tok:
    case Lex.Tok{+k, +tx, +ln, +cl}:
      match wk:
        case Wrap.Walk{+mode, +paren, +bracket, +brace, +angle, +shut, +open, +on, +pline, +pend, +pcol, +spans}:
          +ticks = Wrap.check.ticks_of(tx)
          +act = Wrap.check.act(mode, k, tx, glued, paren, angle, brace, bracket)
          +spec = Laws.wrap.motion(mode, k, tx, glued, paren, bracket, brace, angle)
          wrap.on_sig(Lex.significant(k), Lex.Tok{k, tx, ln, cl},
            Wrap.Walk{mode, paren, bracket, brace, angle, shut, open, on, pline, pend, pcol, spans}, glued,
            Laws.wrap.move(spec, mode, paren, bracket, brace, angle, open, wrap.line_of(shut),
              wrap.cur_of(on, pline, pend, pcol), spans, ln, cl, ticks),
            Equal.trans(Laws.wrap.Read,
              wrap.of(Wrap.check.maybe_note(Wrap.check.is_sep(act),
                Wrap.check.apply(act, Wrap.Walk{mode, paren, bracket, brace, angle, shut, open, on, pline, pend, pcol,
                  spans}, ln, cl, ticks), Lex.Tok{k, tx, ln, cl})),
              Laws.wrap.move(act, mode, paren, bracket, brace, angle, open, wrap.line_of(shut),
                wrap.cur_of(on, pline, pend, pcol), spans, ln, cl, ticks),
              Laws.wrap.move(spec, mode, paren, bracket, brace, angle, open, wrap.line_of(shut),
                wrap.cur_of(on, pline, pend, pcol), spans, ln, cl, ticks),
              wrap.moved(act, mode, on, paren, bracket, brace, angle, shut, open, pline, pend, pcol, spans, k, tx, ln,
                cl, ticks),
              Equal.cong(Wrap.Act, Laws.wrap.Read,
                a => Laws.wrap.move(a, mode, paren, bracket, brace, angle, open, wrap.line_of(shut),
                  wrap.cur_of(on, pline, pend, pcol), spans, ln, cl, ticks),
                act, spec,
                Equal.sym(Wrap.Act, spec, act, wrap.motion(mode, k, tx, glued, paren, bracket, brace, angle)))))

# the end of the header: the parameter still open is done
law wrap.sealed:
  for +wk: Wrap.Walk
  for +glued: Bool
  {wrap.of(Wrap.check.seal(wk)) == Laws.wrap.run([], wrap.of(wk), glued) : Laws.wrap.Read}

def wrap.sealed(wk, _glued):
  match wk:
    case Wrap.Walk{mode, paren, bracket, brace, angle, shut, open, on, pline, pend, pcol, spans}:
      match on:
        case True{}:
          {==}
        case False{}:
          {==}

# the whole header: the rule's walk is the spec's read, from any state
law wrap.walked:
  for toks: List<&2, Lex.Tok>
  for +wk: Wrap.Walk
  for +glued: Bool
  {wrap.of(Wrap.check.walk(toks, wk, glued)) == Laws.wrap.run(toks, wrap.of(wk), glued) : Laws.wrap.Read}

def wrap.walked(toks, wk, glued):
  match toks:
    case Nil{}:
      wrap.sealed(wk, glued)
    case Con{Lex.Tok{+k, +tx, +ln, +cl}, +rest}:
      +tok = {Lex.Tok{k, tx, ln, cl} : Lex.Tok}
      Equal.trans(Laws.wrap.Read,
        wrap.of(Wrap.check.walk(rest, Wrap.check.step(tok, wk, glued), Lex.is_name(k))),
        Laws.wrap.run(rest, wrap.of(Wrap.check.step(tok, wk, glued)), Lex.is_name(k)),
        Laws.wrap.run(rest, Laws.wrap.step(tok, wrap.of(wk), glued), Lex.is_name(k)),
        wrap.walked(rest, Wrap.check.step(tok, wk, glued), Lex.is_name(k)),
        Equal.cong(Laws.wrap.Read, Laws.wrap.Read, rd => Laws.wrap.run(rest, rd, Lex.is_name(k)),
          wrap.of(Wrap.check.step(tok, wk, glued)), Laws.wrap.step(tok, wrap.of(wk), glued),
          wrap.stepped(tok, wk, glued)))

# a Maybe that holds a value
def wrap.found(m: Maybe<&2, Wrap.Span>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{_sp}:
      True{}

# the rule's line test is the spec's
law wrap.shares:
  for ps: List<&2, Wrap.Span>
  for +ln: U32
  {Wrap.check.shares(ps, ln) == Laws.wrap.starts_on(ps, ln) : Bool}

def wrap.shares(ps, ln):
  match ps:
    case Nil{}:
      {==}
    case Con{Wrap.Span{+line, _end, _col}, +rest}:
      M1.put.or(U32.is_eq(line, ln), Wrap.check.shares(rest, ln), Laws.wrap.starts_on(rest, ln), wrap.shares(rest, ln))

# the rule's misplaced parameter is the spec's
law wrap.bad:
  for +line: U32
  for +end: U32
  for +col: U32
  for +open: U32
  for +rest: List<&2, Wrap.Span>
  {Wrap.check.bad(Wrap.Span{line, end, col}, open, rest)
    == Bool.or(Bool.not(U32.is_eq(line, end)), Bool.or(U32.is_eq(line, open), Laws.wrap.starts_on(rest, line))) : Bool}

def wrap.bad(line, end, _col, open, rest):
  M1.put.or(Bool.not(U32.is_eq(line, end)), Lazy.or_else(U32.is_eq(line, open), _u2 => Wrap.check.shares(rest, line)),
    Bool.or(U32.is_eq(line, open), Laws.wrap.starts_on(rest, line)),
    M1.put.or(U32.is_eq(line, open), Wrap.check.shares(rest, line), Laws.wrap.starts_on(rest, line),
      wrap.shares(rest, line)))

# an early exit to a found value is found when it exits, else when the rest is
law wrap.stop_found:
  for b: Bool
  for -sp: Wrap.Span
  for -x: Maybe<&2, Wrap.Span>
  for -y: Bool
  for e: {wrap.found(x) == y : Bool}
  {wrap.found(Lazy.stop(Maybe<&2, Wrap.Span>, b, Some{sp}, _u => x)) == Bool.or(b, y) : Bool}

def wrap.stop_found(b, _sp, _x, _y, e):
  match b:
    case True{}:
      {==}
    case False{}:
      e

# equal disjuncts give equal ors
law wrap.or2:
  for -a: Bool
  for -b: Bool
  for -c: Bool
  for -d: Bool
  for e1: {a == c : Bool}
  for e2: {b == d : Bool}
  {Bool.or(a, b) == Bool.or(c, d) : Bool}

def wrap.or2(a, b, _c, d, e1, e2):
  %e1 : {Bool.or(a, b) == Bool.or(_, d) : Bool}
  %e2 : {Bool.or(a, b) == Bool.or(a, _) : Bool}
  {==}

# the rule finds a misplaced parameter exactly when the spec does
law wrap.judged:
  for ps: List<&2, Wrap.Span>
  for +open: U32
  {wrap.found(Wrap.check.judge(ps, open)) == Laws.wrap.misplaced(ps, open) : Bool}

def wrap.judged(ps, open):
  match ps:
    case Nil{}:
      {==}
    case Con{Wrap.Span{+line, +end, +col}, +rest}:
      Equal.trans(Bool,
        wrap.found(Lazy.stop(Maybe<&2, Wrap.Span>, Wrap.check.bad(Wrap.Span{line, end, col}, open, rest),
          Some{Wrap.Span{line, end, col}}, _u => Wrap.check.judge(rest, open))),
        Bool.or(Wrap.check.bad(Wrap.Span{line, end, col}, open, rest), Laws.wrap.misplaced(rest, open)),
        Laws.wrap.misplaced(Wrap.Span{line, end, col} <> rest, open),
        wrap.stop_found(Wrap.check.bad(Wrap.Span{line, end, col}, open, rest), Wrap.Span{line, end, col},
          Wrap.check.judge(rest, open), Laws.wrap.misplaced(rest, open), wrap.judged(rest, open)),
        wrap.or2(Wrap.check.bad(Wrap.Span{line, end, col}, open, rest), Laws.wrap.misplaced(rest, open),
          Bool.or(Bool.not(U32.is_eq(line, end)), Bool.or(U32.is_eq(line, open), Laws.wrap.starts_on(rest, line))),
          Laws.wrap.misplaced(rest, open), wrap.bad(line, end, col, open, rest), {==}))

# a pick between a found value and none is found when it picks the first
law wrap.pick_found:
  for t: Bool
  for -sp: Wrap.Span
  {wrap.found(Bool.pick(Maybe<&2, Wrap.Span>, t, Some{sp}, None{})) == t : Bool}

def wrap.pick_found(t, _sp):
  match t:
    case True{}:
      {==}
    case False{}:
      {==}

# the rule's last-line test is the spec's
law wrap.tight:
  for ps: List<&2, Wrap.Span>
  for +shut: U32
  {Wrap.check.tight(ps, shut) == Laws.wrap.tight(ps, shut) : Bool}

def wrap.tight(ps, _shut):
  match ps:
    case Nil{}:
      {==}
    case Con{Wrap.Span{line, end, col}, rest}:
      {==}

# a `)` on the line given is found cramped exactly when the spec's test says so
law wrap.tight_found:
  for +line: U32
  for +end: U32
  for +col: U32
  for +spans: List<&2, Wrap.Span>
  {wrap.found(Wrap.check.shut_at(Wrap.Span{line, end, col}, spans)) == Laws.wrap.tight(spans, line) : Bool}

def wrap.tight_found(line, end, col, spans):
  Equal.trans(Bool,
    wrap.found(Bool.pick(Maybe<&2, Wrap.Span>, Wrap.check.tight(spans, line), Some{Wrap.Span{line, end, col}},
      None{})),
    Wrap.check.tight(spans, line),
    Laws.wrap.tight(spans, line),
    wrap.pick_found(Wrap.check.tight(spans, line), Wrap.Span{line, end, col}),
    wrap.tight(spans, line))

# no parameter: found at the `(` line exactly when the spec says none
law wrap.none:
  for spans: List<&2, Wrap.Span>
  for +open: U32
  {wrap.found(Wrap.check.none_at(spans, open)) == Laws.wrap.none(spans) : Bool}

def wrap.none(spans, _open):
  match spans:
    case Nil{}:
      {==}
    case Con{sp, rest}:
      {==}

# the rule finds a cramped `)` exactly when the spec does
law wrap.shut:
  for mode: Wrap.Phase
  for +shut: Wrap.Span
  for +spans: List<&2, Wrap.Span>
  for -paren: U32
  for -bracket: U32
  for -brace: U32
  for -angle: U32
  for -open: U32
  for -on: Bool
  for -pline: U32
  for -pend: U32
  for -pcol: U32
  {wrap.found(Wrap.check.shut_span(Wrap.Walk{mode, paren, bracket, brace, angle, shut, open, on, pline, pend, pcol,
    spans}))
    == Laws.wrap.cramped(mode, wrap.line_of(shut), spans) : Bool}

def wrap.shut(mode, shut, spans, _paren, _bracket, _brace, _angle, _open, _on, _pline, _pend, _pcol):
  match mode:
    case Wrap.Past{}:
      match shut:
        case Wrap.Span{+line, +end, +col}:
          wrap.tight_found(line, end, col, spans)
    case Wrap.Shut{}:
      match shut:
        case Wrap.Span{+line, +end, +col}:
          wrap.tight_found(line, end, col, spans)
    case Wrap.Loose{}:
      match shut:
        case Wrap.Span{+line, +end, +col}:
          wrap.tight_found(line, end, col, spans)
    case Wrap.Seek{}:
      {==}
    case Wrap.Args{}:
      {==}

# the rule finds an empty list exactly when the spec does
law wrap.empty:
  for mode: Wrap.Phase
  for +spans: List<&2, Wrap.Span>
  for +open: U32
  for -paren: U32
  for -bracket: U32
  for -brace: U32
  for -angle: U32
  for -shut: Wrap.Span
  for -on: Bool
  for -pline: U32
  for -pend: U32
  for -pcol: U32
  {wrap.found(Wrap.check.empty_span(Wrap.Walk{mode, paren, bracket, brace, angle, shut, open, on, pline, pend, pcol,
    spans})) == Laws.wrap.empty(mode, spans) : Bool}

def wrap.empty(mode, spans, open, _paren, _bracket, _brace, _angle, _shut, _on, _pline, _pend, _pcol):
  match mode:
    case Wrap.Seek{}:
      {==}
    case Wrap.Args{}:
      wrap.none(spans, open)
    case Wrap.Past{}:
      wrap.none(spans, open)
    case Wrap.Shut{}:
      wrap.none(spans, open)
    case Wrap.Loose{}:
      wrap.none(spans, open)

# the rule finds a `)` with no `->` after it exactly when the spec does
law wrap.loose:
  for mode: Wrap.Phase
  for -spans: List<&2, Wrap.Span>
  for -open: U32
  for -paren: U32
  for -bracket: U32
  for -brace: U32
  for -angle: U32
  for -shut: Wrap.Span
  for -on: Bool
  for -pline: U32
  for -pend: U32
  for -pcol: U32
  {wrap.found(Wrap.check.loose_span(Wrap.Walk{mode, paren, bracket, brace, angle, shut, open, on, pline, pend, pcol,
    spans})) == Laws.wrap.loose(mode) : Bool}

def wrap.loose(mode, _spans, _open, _paren, _bracket, _brace, _angle, _shut, _on, _pline, _pend, _pcol):
  match mode:
    case Wrap.Seek{}:
      {==}
    case Wrap.Args{}:
      {==}
    case Wrap.Past{}:
      {==}
    case Wrap.Shut{}:
      {==}
    case Wrap.Loose{}:
      {==}

# the rule's four findings for a header read are the spec's verdict on it
law wrap.verdict:
  for +wk: Wrap.Walk
  {Bool.or(wrap.found(Wrap.check.jam_span(wk)), Bool.or(wrap.found(Wrap.check.empty_span(wk)),
    Bool.or(wrap.found(Wrap.check.shut_span(wk)), wrap.found(Wrap.check.loose_span(wk)))))
    == Laws.wrap.bad_shape(wrap.of(wk)) : Bool}

def wrap.verdict(wk):
  match wk:
    case Wrap.Walk{+mode, +paren, +bracket, +brace, +angle, +shut, +open, +on, +pline, +pend, +pcol, +spans}:
      +w = {Wrap.Walk{mode, paren, bracket, brace, angle, shut, open, on, pline, pend, pcol, spans} : Wrap.Walk}
      wrap.or2(wrap.found(Wrap.check.judge(List.reverse(&2, Wrap.Span, spans), open)),
        Bool.or(wrap.found(Wrap.check.empty_span(w)),
          Bool.or(wrap.found(Wrap.check.shut_span(w)), wrap.found(Wrap.check.loose_span(w)))),
        Laws.wrap.misplaced(List.reverse(&2, Wrap.Span, spans), open),
        Bool.or(Laws.wrap.empty(mode, spans),
          Bool.or(Laws.wrap.cramped(mode, wrap.line_of(shut), spans), Laws.wrap.loose(mode))),
        wrap.judged(List.reverse(&2, Wrap.Span, spans), open),
        wrap.or2(wrap.found(Wrap.check.empty_span(w)),
          Bool.or(wrap.found(Wrap.check.shut_span(w)), wrap.found(Wrap.check.loose_span(w))),
          Laws.wrap.empty(mode, spans),
          Bool.or(Laws.wrap.cramped(mode, wrap.line_of(shut), spans), Laws.wrap.loose(mode)),
          wrap.empty(mode, spans, open, paren, bracket, brace, angle, shut, on, pline, pend, pcol),
          wrap.or2(wrap.found(Wrap.check.shut_span(w)), wrap.found(Wrap.check.loose_span(w)),
            Laws.wrap.cramped(mode, wrap.line_of(shut), spans), Laws.wrap.loose(mode),
            wrap.shut(mode, shut, spans, paren, bracket, brace, angle, open, on, pline, pend, pcol),
            wrap.loose(mode, spans, open, paren, bracket, brace, angle, shut, on, pline, pend, pcol))))

# the rule's four findings, first found first: one onto the rest when any
# is found, else the rest
law wrap.placed:
  for m: Maybe<&2, Wrap.Span>
  for em: Maybe<&2, Wrap.Span>
  for sh: Maybe<&2, Wrap.Span>
  for lo: Maybe<&2, Wrap.Span>
  for +base: U32
  for +path: String
  for +more: List<&2, F.Finding>
  {List.length(&2, F.Finding, Wrap.check.place(m, em, sh, lo, base, path, more))
    == Bool.pick(Nat, Bool.or(wrap.found(m), Bool.or(wrap.found(em), Bool.or(wrap.found(sh), wrap.found(lo)))),
      1n+List.length(&2, F.Finding, more), List.length(&2, F.Finding, more)) : Nat}

def wrap.placed(m, em, sh, lo, _base, _path, _more):
  match m:
    case Some{Wrap.Span{line, end, col}}:
      {==}
    case None{}:
      match em:
        case Some{Wrap.Span{line, end, col}}:
          {==}
        case None{}:
          match sh:
            case Some{Wrap.Span{line, end, col}}:
              {==}
            case None{}:
              match lo:
                case Some{Wrap.Span{line, end, col}}:
                  {==}
                case None{}:
                  {==}

# a broken header: one finding onto the rest exactly when its shape is bad
law wrap.jammed:
  for +toks: List<&2, Lex.Tok>
  for +line: U32
  for +path: String
  for +more: List<&2, F.Finding>
  {List.length(&2, F.Finding, Wrap.check.jam(line, toks, path, more))
    == Bool.pick(Nat, Laws.wrap.shape(toks), 1n+List.length(&2, F.Finding, more), List.length(&2, F.Finding, more))
    : Nat}

def wrap.jammed(toks, line, path, more):
  +wk = Wrap.check.walk(toks, Wrap.check.start(), False{})
  +len = List.length(&2, F.Finding, more)
  +any = Bool.or(wrap.found(Wrap.check.jam_span(wk)), Bool.or(wrap.found(Wrap.check.empty_span(wk)),
    Bool.or(wrap.found(Wrap.check.shut_span(wk)), wrap.found(Wrap.check.loose_span(wk)))))
  Equal.trans(Nat,
    List.length(&2, F.Finding, Wrap.check.place(Wrap.check.jam_span(wk), Wrap.check.empty_span(wk),
      Wrap.check.shut_span(wk), Wrap.check.loose_span(wk), line, path, more)),
    Bool.pick(Nat, any, 1n+len, len),
    Bool.pick(Nat, Laws.wrap.shape(toks), 1n+len, len),
    wrap.placed(Wrap.check.jam_span(wk), Wrap.check.empty_span(wk), Wrap.check.shut_span(wk), Wrap.check.loose_span(wk),
      line, path, more),
    Equal.cong(Bool, Nat, b => Bool.pick(Nat, b, 1n+len, len), any, Laws.wrap.shape(toks),
      Equal.trans(Bool, any, Laws.wrap.bad_shape(wrap.of(wk)), Laws.wrap.shape(toks), wrap.verdict(wk),
        Equal.cong(Laws.wrap.Read, Bool, rd => Laws.wrap.bad_shape(rd), wrap.of(wk),
          Laws.wrap.run(toks, Laws.wrap.start(), False{}), wrap.walked(toks, Wrap.check.start(), False{})))))

def Laws.wrap_shape_counts(toks, line, path):
  wrap.jammed(toks, line, path, [])

# an early exit to one finding onto the rest, else the rest
law wrap.stop_len:
  for b: Bool
  for -x: F.Finding
  for +more: List<&2, F.Finding>
  {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, b, x <> more, _u => more))
    == Bool.pick(Nat, b, 1n+List.length(&2, F.Finding, more), List.length(&2, F.Finding, more)) : Nat}

def wrap.stop_len(b, _x, _more):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# a one-line header: one finding onto the rest exactly when it is too wide
law wrap.wide:
  for +line: U32
  for +toks: List<&2, Lex.Tok>
  for +path: String
  for +more: List<&2, F.Finding>
  {List.length(&2, F.Finding, Wrap.check.wide(line, toks, path, more))
    == Bool.pick(Nat, U32.is_gt(Laws.wrap.width(toks), 120), 1n+List.length(&2, F.Finding, more),
      List.length(&2, F.Finding, more)) : Nat}

def wrap.wide(line, toks, path, more):
  +len = List.length(&2, F.Finding, more)
  Equal.trans(Nat,
    List.length(&2, F.Finding, Wrap.check.wide(line, toks, path, more)),
    Bool.pick(Nat, U32.is_gt(Wrap.check.width(toks), 120), 1n+len, len),
    Bool.pick(Nat, U32.is_gt(Laws.wrap.width(toks), 120), 1n+len, len),
    wrap.stop_len(U32.is_gt(Wrap.check.width(toks), 120),
      F.Finding{path, line, 120, 0, "wrap",
          "This def header is longer than 120 characters; wrap it with one parameter per line."},
      more),
    Equal.cong(U32, Nat, w => Bool.pick(Nat, U32.is_gt(w, 120), 1n+len, len), Wrap.check.width(toks),
      Laws.wrap.width(toks), Laws.wrap_width(toks)))

# a header, broken or not: one finding onto the rest exactly when it is bad
law wrap.headed:
  for multi: Bool
  for +line: U32
  for +toks: List<&2, Lex.Tok>
  for +path: String
  for +more: List<&2, F.Finding>
  {List.length(&2, F.Finding, Wrap.check.header(multi, line, toks, path, more))
    == Bool.pick(Nat, Bool.pick(Bool, multi, Laws.wrap.shape(toks),
      U32.is_gt(Laws.wrap.width(toks), 120)), 1n+List.length(&2, F.Finding, more),
      List.length(&2, F.Finding, more)) : Nat}

def wrap.headed(multi, line, toks, path, more):
  match multi:
    case True{}:
      wrap.jammed(toks, line, path, more)
    case False{}:
      wrap.wide(line, toks, path, more)

# the rule's line test is the spec's: some token is a newline
law wrap.broken:
  for toks: List<&2, Lex.Tok>
  {Wrap.check.broken(toks) == Laws.wrap.lines(toks) : Bool}

def wrap.broken(toks):
  match toks:
    case Nil{}:
      {==}
    case Con{Lex.Tok{+k, _tx, _ln, _cl}, +rest}:
      M1.put.or(Lex.is_nl(k), Wrap.check.broken(rest), Laws.wrap.lines(rest), wrap.broken(rest))

# an item: one finding onto the rest exactly when it is a bad def header
law wrap.one:
  for k: Outline.ItemKind
  for +line: U32
  for +sig: String
  for +path: String
  for +more: List<&2, F.Finding>
  {List.length(&2, F.Finding, Wrap.check.one(k, line, sig, path, more))
    == Bool.pick(Nat, Bool.and(Outline.is_def(k), Laws.wrap.bad(sig)), 1n+List.length(&2, F.Finding, more),
      List.length(&2, F.Finding, more)) : Nat}

def wrap.one(k, line, sig, path, more):
  match k:
    case Outline.IImport{}:
      {==}
    case Outline.IDef{}:
      +toks = Lex.tokens(sig)
      +len = List.length(&2, F.Finding, more)
      Equal.trans(Nat,
        List.length(&2, F.Finding, Wrap.check.header(Wrap.check.broken(toks), line, toks, path, more)),
        Bool.pick(Nat, Bool.pick(Bool, Wrap.check.broken(toks), Laws.wrap.shape(toks),
          U32.is_gt(Laws.wrap.width(toks), 120)), 1n+len, len),
        Bool.pick(Nat, Bool.pick(Bool, Laws.wrap.lines(toks), Laws.wrap.shape(toks),
          U32.is_gt(Laws.wrap.width(toks), 120)), 1n+len, len),
        wrap.headed(Wrap.check.broken(toks), line, toks, path, more),
        Equal.cong(Bool, Nat, b => Bool.pick(Nat, Bool.pick(Bool, b, Laws.wrap.shape(toks),
          U32.is_gt(Laws.wrap.width(toks), 120)), 1n+len, len), Wrap.check.broken(toks), Laws.wrap.lines(toks),
          wrap.broken(toks)))
    case Outline.ILaw{}:
      {==}
    case Outline.IType{}:
      {==}
    case Outline.ICtor{}:
      {==}
    case Outline.ILocal{}:
      {==}

# the rule's walk over the items counts the bad def headers
law wrap.went:
  for items: List<&2, Outline.Item>
  for +path: String
  {List.length(&2, F.Finding, Wrap.check.go(items, path)) == Laws.wrap.count(items) : Nat}

def wrap.went(items, path):
  match items:
    case Nil{}:
      {==}
    case Con{Outline.Item{+k, _name, +line, +sig, _doc, _pp}, +rest}:
      +more = Wrap.check.go(rest, path)
      +hit = Bool.and(Outline.is_def(k), Laws.wrap.bad(sig))
      Equal.trans(Nat,
        List.length(&2, F.Finding, Wrap.check.one(k, line, sig, path, more)),
        Bool.pick(Nat, hit, 1n+List.length(&2, F.Finding, more), List.length(&2, F.Finding, more)),
        Bool.pick(Nat, hit, 1n+Laws.wrap.count(rest), Laws.wrap.count(rest)),
        wrap.one(k, line, sig, path, more),
        Equal.cong(Nat, Nat, nn => Bool.pick(Nat, hit, 1n+nn, nn), List.length(&2, F.Finding, more),
          Laws.wrap.count(rest), wrap.went(rest, path)))

def Laws.wrap_counts(path, _text, _toks, _tree, _bound, items):
  wrap.went(items, path)
