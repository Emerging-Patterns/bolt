# rule wrap: how a def header breaks. A one-line header wider than 120 must
# break; the width is the header through its `:`, counted the way `space`
# counts a line (a string literal is two characters). A one-line header that
# fits stays one line however many parameters it has. A header that breaks
# puts `(` at the end of the first line and one parameter on each following
# line, then `)` and the return type on a line of their own after the last
# parameter. Several parameters on a line, a parameter left on the `(`
# line, a parameter split across lines, or a `)` on the last parameter's line
# (`bb: U32) -> U32:`), is a finding. A comment after the header's `:` is not
# part of the header: `def u(aa: U32) -> U32: # note` is a one-line header.
import Base
import ../../src.bend as Src
import ../../finding.bend as F
import ../../../syntax/lex.bend as Lex
import ../../../syntax/outline.bend as Outline
import ../../../lazy/lazy.bend as Lazy
import ./space.bend as Space

# where one parameter sits in the header: its first line, its last, its column
type Span is Data:
  Span{line: U32, end: U32, col: U32}

# seeking the parameter list, inside it, or past its `)`
type Phase is Data:
  Seek{}
  Args{}
  Past{}

# what a token does to the bracket depths
type Act is Data:
  AOpen{}
  AParen{}
  AEnd{}
  AUnparen{}
  ABrack{}
  AUnbrack{}
  ABrace{}
  AUnbrace{}
  AAngle{}
  AUnangle{}
  AComma{}
  ANone{}

# the walk: depths, where the list's `)` sat, the `(` line, and the parameter
# open so far (spans reversed)
type Walk is Data:
  Walk{mode: Phase, paren: U32, bracket: U32, brace: U32, angle: U32, shut: Span, open: U32,
    on: Bool, pline: U32, pend: U32, pcol: U32, spans: List<&2, Span>}

# the header already breaks across lines
def check.broken(+sig: String) -> Bool:
  String.contains(sig, "\n")

# one token's share of the header's width
def check.add(+acc: U32, kd: Lex.TokKind, +tx: String) -> U32:
  (acc + Space.width_of(kd, tx) : U32)

# a `:` token?
def check.is_colon(kk: Lex.TokKind) -> Bool:
  match kk:
    case Lex.TColon{}:
      True{}
    case other:
      False{}

# the header's width through its last `:` (upto, once seen says there was
# one), else its whole width, a string literal counting as two
def check.width.go(toks: List<&2, Lex.Tok>, +acc: U32, +upto: U32, +seen: Bool) -> U32:
  match toks:
    case Nil{}:
      Bool.pick(U32, seen, upto, acc)
    case Con{Lex.Tok{+kd, tx, _ln, _cl}, rest}:
      +next = check.add(acc, kd, tx)
      +colon = check.is_colon(kd)
      check.width.go(rest, next, Bool.pick(U32, colon, next, upto), Bool.or(colon, seen))

# the header's width, through its `:`: a comment after it does not count
def check.width(+sig: String) -> U32:
  check.width.go(Lex.tokens(sig), 0, 0, False{})

# a fresh walk, before the parameter list
def check.start() -> Walk:
  Walk{Seek{}, 0, 0, 0, 0, Span{0, 0, 0}, 0, False{}, 0, 0, 0, []}

# `(`
def check.is_oparen(kk: Lex.TokKind, +tx: String) -> Bool:
  match kk:
    case Lex.TOpen{}:
      String.eq(tx, "(")
    case other:
      False{}

# `)`
def check.is_cparen(kk: Lex.TokKind, +tx: String) -> Bool:
  match kk:
    case Lex.TClose{}:
      String.eq(tx, ")")
    case other:
      False{}

# an opening bracket, as the depth it raises; ANone when it is not one
def check.open_text(+tx: String) -> Act:
  Bool.pick(Act, String.eq(tx, "("), AParen{},
    Bool.pick(Act, String.eq(tx, "["), ABrack{},
      Bool.pick(Act, String.eq(tx, "{"), ABrace{}, ANone{})))

# an opening bracket, as the depth it raises
def check.on_open(kk: Lex.TokKind, +tx: String) -> Act:
  match kk:
    case Lex.TOpen{}:
      check.open_text(tx)
    case other:
      ANone{}

# a closing bracket, as the depth it lowers; ANone when it is not one
def check.close_text(+tx: String) -> Act:
  Bool.pick(Act, String.eq(tx, ")"), AUnparen{},
    Bool.pick(Act, String.eq(tx, "]"), AUnbrack{},
      Bool.pick(Act, String.eq(tx, "}"), AUnbrace{}, ANone{})))

# a closing bracket, as the depth it lowers
def check.on_close(kk: Lex.TokKind, +tx: String) -> Act:
  match kk:
    case Lex.TClose{}:
      check.close_text(tx)
    case other:
      ANone{}

# an operator token
def check.is_op(kk: Lex.TokKind) -> Bool:
  match kk:
    case Lex.TOp{}:
      True{}
    case other:
      False{}

# every char a `>`
def check.gt_chars(cs: List<&2, Char>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{+c, t}:
      Lazy.and_then(Char.is_eq(c, '>'), _u => check.gt_chars(t))

# the text is a non-empty run of `>`
def check.all_gt(+tx: String) -> Bool:
  Bool.and(Bool.not(String.is_empty(tx)), check.gt_chars(String.to_list(tx)))

# how many `>` a run holds
def check.gt_count(cs: List<&2, Char>) -> Nat:
  match cs:
    case Nil{}:
      0n
    case Con{+c, t}:
      +more = check.gt_count(t)
      Bool.pick(Nat, Char.is_eq(c, '>'), Succ{more}, more)

# the angle-closes in the text, else none
def check.ticks_of(+tx: String) -> Nat:
  Lazy.stop(Nat, Bool.not(check.all_gt(tx)), 0n, _u => check.gt_count(String.to_list(tx)))

# `<` or `<&` glued to a name opens type arguments
def check.opens_angle(glued: Bool, +tx: String) -> Bool:
  Bool.and(glued, Bool.or(String.eq(tx, "<"), String.eq(tx, "<&")))

# an angle close, discarded when an angle open already won
def check.drop_close(_closed: Act) -> Act:
  AAngle{}

# an angle open wins over a close; otherwise the close stands
def check.prefer_open(opens: Bool, closed: Act) -> Act:
  match opens:
    case True{}:
      check.drop_close(closed)
    case False{}:
      closed

# `>` runs close angles; `<` glued to a name opens one
def check.op_angle(+tx: String, glued: Bool) -> Act:
  check.prefer_open(check.opens_angle(glued, tx),
    Bool.pick(Act, check.all_gt(tx), AUnangle{}, ANone{}))

# not an operator: no angle motion
def check.no_angle(_tx: String, _glued: Bool) -> Act:
  ANone{}

# an operator's angle motion
def check.angle_op(is_op: Bool, +tx: String, glued: Bool) -> Act:
  match is_op:
    case True{}:
      check.op_angle(tx, glued)
    case False{}:
      check.no_angle(tx, glued)

# angle motion, when the token is an operator
def check.angle_act(kk: Lex.TokKind, +tx: String, glued: Bool) -> Act:
  check.angle_op(check.is_op(kk), tx, glued)

# a value used only so a branch can name it
def check.keep(act: Act, _kk: Lex.TokKind, _tx: String, _glued: Bool) -> Act:
  act

# angle motion when the token was not a bracket, else that bracket
def check.or_angle(closed: Act, kk: Lex.TokKind, +tx: String, glued: Bool) -> Act:
  match closed:
    case ANone{}:
      check.angle_act(kk, tx, glued)
    case other:
      check.keep(other, kk, tx, glued)

# a close bracket, else angle motion
def check.or_close(opened: Act, +kk: Lex.TokKind, +tx: String, glued: Bool) -> Act:
  match opened:
    case ANone{}:
      check.or_angle(check.on_close(kk, tx), kk, tx, glued)
    case other:
      check.keep(other, kk, tx, glued)

# the bracket or angle motion of a token, not the parameter list's own breaks
def check.brackets(+kk: Lex.TokKind, +tx: String, glued: Bool) -> Act:
  check.or_close(check.on_open(kk, tx), kk, tx, glued)

# no depth is open
def check.zero(+paren: U32, +angle: U32, +brace: U32, +bracket: U32) -> Bool:
  Bool.and(U32.is_eq(paren, 0),
    Bool.and(U32.is_eq(angle, 0),
      Bool.and(U32.is_eq(brace, 0), U32.is_eq(bracket, 0))))

# the top of the parameter list: one `(`, nothing nested
def check.top(+paren: U32, +angle: U32, +brace: U32, +bracket: U32) -> Bool:
  Bool.and(U32.is_eq(paren, 1),
    Bool.and(U32.is_eq(angle, 0),
      Bool.and(U32.is_eq(brace, 0), U32.is_eq(bracket, 0))))

# `(` at depth zero opens the parameter list; a nested one is just a paren
def check.pick_open(zero: Bool, rest: Act) -> Act:
  match zero:
    case True{}:
      AOpen{}
    case False{}:
      rest

# the parameter list's `(`, else the token's ordinary motion
def check.seek_open(is_open: Bool, zero: Bool, rest: Act) -> Act:
  match is_open:
    case True{}:
      check.pick_open(zero, rest)
    case False{}:
      rest

# motion while still seeking the parameter list
def check.act_seek(
  +kk: Lex.TokKind,
  +tx: String,
  glued: Bool,
  +paren: U32,
  +angle: U32,
  +brace: U32,
  +bracket: U32
) -> Act:
  check.seek_open(check.is_oparen(kk, tx), check.zero(paren, angle, brace, bracket),
    check.brackets(kk, tx, glued))

# `)` at the top of the list ends it; a nested one is just a paren
def check.end_or(flat: Bool, rest: Act) -> Act:
  match flat:
    case True{}:
      AEnd{}
    case False{}:
      rest

# the parameter list's `)`, else the token's ordinary motion
def check.args_end(is_close: Bool, flat: Bool, rest: Act) -> Act:
  match is_close:
    case True{}:
      check.end_or(flat, rest)
    case False{}:
      rest

# a comma at the top of the list separates parameters
def check.comma_or(flat: Bool, rest: Act) -> Act:
  match flat:
    case True{}:
      AComma{}
    case False{}:
      rest

# a separating comma, else the token's ordinary motion
def check.args_comma(is_comma: Bool, flat: Bool, rest: Act) -> Act:
  match is_comma:
    case True{}:
      check.comma_or(flat, rest)
    case False{}:
      rest

# motion inside the parameter list
def check.act_args(
  +kk: Lex.TokKind,
  +tx: String,
  glued: Bool,
  +paren: U32,
  +angle: U32,
  +brace: U32,
  +bracket: U32
) -> Act:
  check.args_end(check.is_cparen(kk, tx), check.top(paren, angle, brace, bracket),
    check.args_comma(Lex.is_comma(kk), check.top(paren, angle, brace, bracket),
      check.brackets(kk, tx, glued)))

# past the parameter list nothing moves
def check.act_done(
  _kk: Lex.TokKind,
  _tx: String,
  _glued: Bool,
  _paren: U32,
  _angle: U32,
  _brace: U32,
  _bracket: U32
) -> Act:
  ANone{}

# the motion of one token
def check.act(
  ph: Phase,
  kk: Lex.TokKind,
  +tx: String,
  glued: Bool,
  +paren: U32,
  +angle: U32,
  +brace: U32,
  +bracket: U32
) -> Act:
  match ph:
    case Past{}:
      check.act_done(kk, tx, glued, paren, angle, brace, bracket)
    case Seek{}:
      check.act_seek(kk, tx, glued, paren, angle, brace, bracket)
    case Args{}:
      check.act_args(kk, tx, glued, paren, angle, brace, bracket)

# the parameter list's own `(`, `)` and commas are not part of a parameter
def check.is_sep(act: Act) -> Bool:
  match act:
    case AOpen{}:
      True{}
    case AEnd{}:
      True{}
    case AComma{}:
      True{}
    case other:
      False{}

# one less, and not below zero
def check.dec_u(+nn: U32) -> U32:
  Lazy.stop(U32, U32.is_eq(nn, 0), 0, _u => (nn - 1 : U32))

# `left` angle-closes applied to the depth, and not below zero
def check.sub(left: Nat, +angle: U32) -> U32:
  match left:
    case Zero{}:
      angle
    case Succ{p}:
      Lazy.stop(U32, U32.is_eq(angle, 0), angle, _u => check.sub(p, (angle - 1 : U32)))

# a parameter that did start, onto the list
def check.no_span(_pline: U32, _pend: U32, _pcol: U32, spans: List<&2, Span>) -> List<&2, Span>:
  spans

# the open parameter, closed onto the list
def check.cons(on: Bool, +pline: U32, +pend: U32, +pcol: U32, spans: List<&2, Span>) -> List<&2, Span>:
  match on:
    case True{}:
      Span{pline, pend, pcol} <> spans
    case False{}:
      check.no_span(pline, pend, pcol, spans)

# the walk rebuilt; angle-closes are applied by the caller
def check.rebuild(
  _ticks: Nat,
  mode: Phase,
  paren: U32,
  bracket: U32,
  brace: U32,
  angle: U32,
  shut: Span,
  open: U32,
  on: Bool,
  pline: U32,
  pend: U32,
  pcol: U32,
  spans: List<&2, Span>
) -> Walk:
  Walk{mode, paren, bracket, brace, angle, shut, open, on, pline, pend, pcol, spans}

# `(` opens the parameter list
def check.opened(
  ticks: Nat,
  bracket: U32,
  brace: U32,
  angle: U32,
  spans: List<&2, Span>,
  +ln: U32,
  _mode: Phase,
  _paren: U32,
  _shut: Span,
  _open: U32,
  _on: Bool,
  _pline: U32,
  _pend: U32,
  _pcol: U32
) -> Walk:
  check.rebuild(ticks, Args{}, 1, bracket, brace, angle, Span{0, 0, 0}, ln, False{}, 0, 0, 0, spans)

# `)` ends the parameter list, and notes where it sits
def check.ended(
  ticks: Nat,
  _mode: Phase,
  paren: U32,
  bracket: U32,
  brace: U32,
  angle: U32,
  _shut: Span,
  open: U32,
  on: Bool,
  pline: U32,
  pend: U32,
  pcol: U32,
  spans: List<&2, Span>,
  +ln: U32,
  cl: U32
) -> Walk:
  check.rebuild(ticks, Past{}, check.dec_u(paren), bracket, brace, angle, Span{ln, ln, cl}, open, False{},
    0, 0, 0, check.cons(on, pline, pend, pcol, spans))

# a comma closes the parameter that was open
def check.commaed(
  ticks: Nat,
  mode: Phase,
  paren: U32,
  bracket: U32,
  brace: U32,
  angle: U32,
  shut: Span,
  open: U32,
  on: Bool,
  pline: U32,
  pend: U32,
  pcol: U32,
  spans: List<&2, Span>
) -> Walk:
  check.rebuild(ticks, mode, paren, bracket, brace, angle, shut, open, False{}, 0, 0, 0,
    check.cons(on, pline, pend, pcol, spans))

# a run of `>` lowers the angle depth
def check.unangled(
  ticks: Nat,
  mode: Phase,
  paren: U32,
  bracket: U32,
  brace: U32,
  angle: U32,
  shut: Span,
  open: U32,
  on: Bool,
  pline: U32,
  pend: U32,
  pcol: U32,
  spans: List<&2, Span>
) -> Walk:
  check.rebuild(0n, mode, paren, bracket, brace, check.sub(ticks, angle), shut, open, on, pline, pend, pcol, spans)

# the token's motion applied to fields already taken off the walk
def check.apply_on(
  motion: Act,
  mode: Phase,
  paren: U32,
  bracket: U32,
  brace: U32,
  angle: U32,
  shut: Span,
  open: U32,
  on: Bool,
  pline: U32,
  pend: U32,
  pcol: U32,
  spans: List<&2, Span>,
  +ln: U32,
  cl: U32,
  ticks: Nat
) -> Walk:
  match motion:
    case AOpen{}:
      check.opened(ticks, bracket, brace, angle, spans, ln, mode, paren, shut, open, on, pline, pend, pcol)
    case AParen{}:
      check.rebuild(ticks, mode, (paren + 1 : U32), bracket, brace, angle, shut, open, on, pline, pend, pcol, spans)
    case AEnd{}:
      check.ended(ticks, mode, paren, bracket, brace, angle, shut, open, on, pline, pend, pcol, spans, ln, cl)
    case AUnparen{}:
      check.rebuild(ticks, mode, check.dec_u(paren), bracket, brace, angle, shut, open, on, pline, pend, pcol, spans)
    case ABrack{}:
      check.rebuild(ticks, mode, paren, (bracket + 1 : U32), brace, angle, shut, open, on, pline, pend, pcol, spans)
    case AUnbrack{}:
      check.rebuild(ticks, mode, paren, check.dec_u(bracket), brace, angle, shut, open, on, pline, pend, pcol, spans)
    case ABrace{}:
      check.rebuild(ticks, mode, paren, bracket, (brace + 1 : U32), angle, shut, open, on, pline, pend, pcol, spans)
    case AUnbrace{}:
      check.rebuild(ticks, mode, paren, bracket, check.dec_u(brace), angle, shut, open, on, pline, pend, pcol, spans)
    case AAngle{}:
      check.rebuild(ticks, mode, paren, bracket, brace, (angle + 1 : U32), shut, open, on, pline, pend, pcol, spans)
    case AUnangle{}:
      check.unangled(ticks, mode, paren, bracket, brace, angle, shut, open, on, pline, pend, pcol, spans)
    case AComma{}:
      check.commaed(ticks, mode, paren, bracket, brace, angle, shut, open, on, pline, pend, pcol, spans)
    case ANone{}:
      check.rebuild(ticks, mode, paren, bracket, brace, angle, shut, open, on, pline, pend, pcol, spans)

# the token's motion applied to the walk
def check.apply(motion: Act, wk: Walk, +ln: U32, cl: U32, ticks: Nat) -> Walk:
  Walk{mode, paren, bracket, brace, angle, shut, open, on, pline, pend, pcol, spans} = wk
  check.apply_on(motion, mode, paren, bracket, brace, angle, shut, open, on, pline, pend, pcol, spans, ln, cl, ticks)

# the same parameter, extended to this line
def check.note_extend(
  +pline: U32,
  _pend: U32,
  +pcol: U32,
  +ln: U32,
  _cl: U32,
  mode: Phase,
  paren: U32,
  bracket: U32,
  brace: U32,
  angle: U32,
  shut: Span,
  open: U32,
  spans: List<&2, Span>
) -> Walk:
  Walk{mode, paren, bracket, brace, angle, shut, open, True{}, pline, ln, pcol, spans}

# a parameter starting here
def check.note_begin(
  _pline: U32,
  _pend: U32,
  _pcol: U32,
  +ln: U32,
  +cl: U32,
  mode: Phase,
  paren: U32,
  bracket: U32,
  brace: U32,
  angle: U32,
  shut: Span,
  open: U32,
  spans: List<&2, Span>
) -> Walk:
  Walk{mode, paren, bracket, brace, angle, shut, open, True{}, ln, ln, cl, spans}

# the token continues the open parameter, or starts one
def check.note_on(
  on: Bool,
  mode: Phase,
  paren: U32,
  bracket: U32,
  brace: U32,
  angle: U32,
  shut: Span,
  open: U32,
  pline: U32,
  pend: U32,
  pcol: U32,
  spans: List<&2, Span>,
  +ln: U32,
  +cl: U32
) -> Walk:
  match on:
    case True{}:
      check.note_extend(pline, pend, pcol, ln, cl, mode, paren, bracket, brace, angle, shut, open, spans)
    case False{}:
      check.note_begin(pline, pend, pcol, ln, cl, mode, paren, bracket, brace, angle, shut, open, spans)

# outside the parameter list the token starts nothing
def check.note_skip(
  on: Bool,
  mode: Phase,
  paren: U32,
  bracket: U32,
  brace: U32,
  angle: U32,
  shut: Span,
  open: U32,
  pline: U32,
  pend: U32,
  pcol: U32,
  spans: List<&2, Span>,
  _tok: Lex.Tok
) -> Walk:
  Walk{mode, paren, bracket, brace, angle, shut, open, on, pline, pend, pcol, spans}

# inside the parameter list, the token's position joins the open parameter
def check.note_here(
  on: Bool,
  mode: Phase,
  paren: U32,
  bracket: U32,
  brace: U32,
  angle: U32,
  shut: Span,
  open: U32,
  pline: U32,
  pend: U32,
  pcol: U32,
  spans: List<&2, Span>,
  tok: Lex.Tok
) -> Walk:
  Lex.Tok{_kk, _tx, +ln, +cl} = tok
  check.note_on(on, mode, paren, bracket, brace, angle, shut, open, pline, pend, pcol, spans, ln, cl)

# inside the list the token is part of a parameter; outside it is not
def check.note_phase(
  mode: Phase,
  on: Bool,
  paren: U32,
  bracket: U32,
  brace: U32,
  angle: U32,
  shut: Span,
  open: U32,
  pline: U32,
  pend: U32,
  pcol: U32,
  spans: List<&2, Span>,
  tok: Lex.Tok
) -> Walk:
  match mode:
    case Args{}:
      check.note_here(on, Args{}, paren, bracket, brace, angle, shut, open, pline, pend, pcol, spans, tok)
    case other:
      check.note_skip(on, other, paren, bracket, brace, angle, shut, open, pline, pend, pcol, spans, tok)

# a token that belongs to a parameter notes where that parameter sits
def check.note_args(wk: Walk, tok: Lex.Tok) -> Walk:
  Walk{mode, paren, bracket, brace, angle, shut, open, on, pline, pend, pcol, spans} = wk
  check.note_phase(mode, on, paren, bracket, brace, angle, shut, open, pline, pend, pcol, spans, tok)

# a token the parameter list itself consumed
def check.drop_tok(_tok: Lex.Tok, wk: Walk) -> Walk:
  wk

# note the token when it is part of a parameter
def check.maybe_note(sep: Bool, wk: Walk, tok: Lex.Tok) -> Walk:
  match sep:
    case True{}:
      check.drop_tok(tok, wk)
    case False{}:
      check.note_args(wk, tok)

# one significant token
def check.step_hit(+wk: Walk, +tok: Lex.Tok, glued: Bool) -> Walk:
  Walk{+mode, +paren, +bracket, +brace, +angle, _shut, _open, _on, _pline, _pend, _pcol, _spans} = wk
  Lex.Tok{+kk, +tx, +ln, cl} = tok
  +motion = check.act(mode, kk, tx, glued, paren, angle, brace, bracket)
  check.maybe_note(check.is_sep(motion), check.apply(motion, wk, ln, cl, check.ticks_of(tx)), tok)

# a space, a newline or a comment changes nothing
def check.step_skip(_tok: Lex.Tok, wk: Walk, _glued: Bool) -> Walk:
  wk

# a significant token is read; a space, a newline or a comment is not
def check.step_on(sig: Bool, +tok: Lex.Tok, wk: Walk, glued: Bool) -> Walk:
  match sig:
    case True{}:
      check.step_hit(wk, tok, glued)
    case False{}:
      check.step_skip(tok, wk, glued)

# one token of the header
def check.step(+tok: Lex.Tok, wk: Walk, glued: Bool) -> Walk:
  Lex.Tok{+kk, _tx, _ln, _cl} = tok
  check.step_on(Lex.significant(kk), tok, wk, glued)

# the parameter still open at the end of the header
def check.seal(wk: Walk) -> Walk:
  Walk{mode, paren, bracket, brace, angle, shut, open, on, pline, pend, pcol, spans} = wk
  Walk{mode, paren, bracket, brace, angle, shut, open, False{}, 0, 0, 0, check.cons(on, pline, pend, pcol, spans)}

# a name glues a following `<`
def check.glue_of(tok: Lex.Tok) -> Bool:
  Lex.Tok{kk, _tx, _ln, _cl} = tok
  Lex.is_name(kk)

# every token of the header
def check.walk(toks: List<&2, Lex.Tok>, wk: Walk, glued: Bool) -> Walk:
  match toks:
    case Nil{}:
      check.seal(wk)
    case Con{+tok, rest}:
      check.walk(rest, check.step(tok, wk, glued), check.glue_of(tok))

# another parameter already sits on this line
def check.shares(spans: List<&2, Span>, +ln: U32) -> Bool:
  match spans:
    case Nil{}:
      False{}
    case Con{Span{+line, _end, _col}, rest}:
      Lazy.or_else(U32.is_eq(line, ln), _u => check.shares(rest, ln))

# split across lines, sitting on the `(` line, or sharing its line
def check.bad(sp: Span, +open: U32, spans: List<&2, Span>) -> Bool:
  Span{+line, +end, _col} = sp
  Lazy.or_else(Bool.not(U32.is_eq(line, end)),
    _u => Lazy.or_else(U32.is_eq(line, open), _u2 => check.shares(spans, line)))

# the first parameter that is not alone on its own line
def check.judge(spans: List<&2, Span>, +open: U32) -> Maybe<&2, Span>:
  match spans:
    case Nil{}:
      None{}
    case Con{+sp, +rest}:
      Lazy.stop(Maybe<&2, Span>, check.bad(sp, open, rest), Some{sp}, _u => check.judge(rest, open))

# the first parameter that breaks the shape, in source order
def check.jam_span(wk: Walk) -> Maybe<&2, Span>:
  Walk{_mode, _paren, _bracket, _brace, _angle, _shut, +open, _on, _pline, _pend, _pcol, spans} = wk
  check.judge(List.reverse(&2, Span, spans), open)

# the last parameter (the head: spans are reversed) runs onto the `)` line
def check.tight(spans: List<&2, Span>, +close: U32) -> Bool:
  match spans:
    case Nil{}:
      False{}
    case Con{Span{_line, +end, _col}, _rest}:
      Bool.not(U32.is_lt(end, close))

# the `)`, when it shares the last parameter's line
def check.shut_at(shut: Span, spans: List<&2, Span>) -> Maybe<&2, Span>:
  Span{+line, end, +col} = shut
  Bool.pick(Maybe<&2, Span>, check.tight(spans, line), Some{Span{line, end, col}}, None{})

# the `)` of a list that did close, when it is not on a line after the last
# parameter
def check.shut_span(wk: Walk) -> Maybe<&2, Span>:
  Walk{mode, _paren, _bracket, _brace, _angle, shut, _open, _on, _pline, _pend, _pcol, spans} = wk
  match mode:
    case Past{}:
      check.shut_at(shut, spans)
    case other:
      None{}

# the `)` on the last parameter's line, as a finding
def check.place_shut(
  mm: Maybe<&2, Span>,
  +base: U32,
  +path: String,
  +more: List<&2, F.Finding>
) -> List<&2, F.Finding>:
  match mm:
    case None{}:
      more
    case Some{Span{+line, _end, +col}}:
      F.Finding{path, (base + line : U32), col, 0, "wrap",
        "Def header does not close on its own line; put `)` and the return type on the line after the last parameter."}
        <> more

# the parameter that breaks the shape, else a misplaced `)`, as a finding on
# the header's lines
def check.place(
  mm: Maybe<&2, Span>,
  shut: Maybe<&2, Span>,
  +base: U32,
  +path: String,
  +more: List<&2, F.Finding>
) -> List<&2, F.Finding>:
  match mm:
    case None{}:
      check.place_shut(shut, base, path, more)
    case Some{Span{+line, _end, +col}}:
      F.Finding{path, (base + line : U32), col, 0, "wrap",
        "Def header is not one parameter per line; put one parameter on each line within the 120-character limit."}
        <> more

# a multi-line header that is not one parameter per line, or whose `)` shares
# the last parameter's line
def check.jam(+line: U32, toks: List<&2, Lex.Tok>, +path: String, +more: List<&2, F.Finding>) -> List<&2, F.Finding>:
  +wk = check.walk(toks, check.start(), False{})
  check.place(check.jam_span(wk), check.shut_span(wk), line, path, more)

# a one-line header past 120
def check.wide(+line: U32, +sig: String, +path: String, +more: List<&2, F.Finding>) -> List<&2, F.Finding>:
  Lazy.stop(List<&2, F.Finding>, U32.is_gt(check.width(sig), 120),
    F.Finding{path, line, 120, 0, "wrap",
      "Def header exceeds the 120-character limit; wrap with one parameter per line."} <> more, _u => more)

# a broken header is judged by its shape; a one-line header by its width
def check.header(
  multi: Bool,
  +line: U32,
  +sig: String,
  +path: String,
  +more: List<&2, F.Finding>
) -> List<&2, F.Finding>:
  match multi:
    case True{}:
      check.jam(line, Lex.tokens(sig), path, more)
    case False{}:
      check.wide(line, sig, path, more)

# a def header; anything else is not this rule's
def check.one(
  kk: Outline.ItemKind,
  +line: U32,
  +sig: String,
  +path: String,
  +more: List<&2, F.Finding>
) -> List<&2, F.Finding>:
  +multi = check.broken(sig)
  Lazy.stop(List<&2, F.Finding>, Bool.not(Outline.is_def(kk)), more,
    _u => check.header(multi, line, sig, path, more))

# every def header of the file
def check.go(items: List<&2, Outline.Item>, +path: String) -> List<&2, F.Finding>:
  match items:
    case Nil{}:
      Nil{}
    case Con{Outline.Item{+kk, _name, +line, +sig, _doc, _pp}, rest}:
      +more = check.go(rest, path)
      check.one(kk, line, sig, path, more)

# the rule
def check(ss: Src.Src) -> List<&2, F.Finding>:
  Src.Src{+path, _text, _toks, _tree, _bound, items} = ss
  check.go(items, path)
