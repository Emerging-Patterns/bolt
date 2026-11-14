# src/fmt/head: the def-header pass of bolt's formatter. A header that
# `wrap` (src/rules/style/wrap.bend) would judge, one that already breaks
# across lines or is wider than 120 on one, is written in the shape that
# rule asks for:
#
#     def name(
#       first: A,
#       second: B
#     ) -> T:
#
# `(` ends the first line, each parameter has a line of its own, indented
# two, and `)` opens the last line with the return type after it. A header
# on one line that fits is left as it is, however many parameters it has. A
# parameter list with no parameter in it is closed where it opens: `()`.
# Only blank space changes: a space or a newline between two tokens of the
# header is dropped or put back, and every other token is kept as it is, in
# order. Inside a parameter the spacing is kept, and a line break there
# becomes one space: none after an opening bracket, none before a closing
# one or a comma, and none before an opening one unless a comma comes right
# before it. A comment stays where it is on its line: after the `(` or a
# comma it keeps that line, two spaces off, and anywhere else it gets a line
# of its own; the line after it starts as the shape says.
# The header runs from a `def` at column 0 through the first `:` outside
# every bracket; a `def` with no such `:` before the tokens end is left
# alone. Which token is the list's `(`, its `)` or a comma between two
# parameters is wrap's reading (its `check.act`), so the two agree on what
# a parameter is.
# Pure.
import Base
import ../lazy/lazy.bend as Lazy
import ../syntax/lex.bend as Lex
import ../rules/style/wrap.bend as Wrap

# what a token of a header is to the layout: the parameter list's `(`, its
# `)`, a comma between two parameters, a comment, another opening bracket,
# another closing bracket, a comma inside a parameter, or anything else
type Role is Data:
  ROpen{}
  REnd{}
  RComma{}
  RNote{}
  RBracket{}
  RClose{}
  RSep{}
  RWord{}

# what the token before was: the list's `(`, a comma between parameters, a
# comment, another opening bracket, a comma inside a parameter, or anything
# else
type Prev is Data:
  POpen{}
  PComma{}
  PNote{}
  PBracket{}
  PSep{}
  PWord{}

# the blank space before a token: none, one space, two, a line break, a line
# break and an indent of two, or the spaces that were there
type Gap is Data:
  GNone{}
  GOne{}
  GTwo{}
  GLine{}
  GDent{}
  GKeep{sp: String}

# where the pass is: outside a header, or inside one it is rewriting, with
# wrap's walk so far, whether the token before was a name, what it was to
# the layout, whether a line break came since, the spaces since, and how
# many brackets are open
type State is Data:
  Out{}
  In{wk: Wrap.Walk, glued: Bool, prev: Prev, brk: Bool, sp: String, depth: U32}

# a space token of this text
def space(text: String) -> Lex.Tok:
  Lex.Tok{Lex.TSpace{}, text, 0, 0}

# a newline token
def newline() -> Lex.Tok:
  Lex.Tok{Lex.TNewline{}, "\n", 0, 0}

# a gap as tokens
def gap.toks(gp: Gap) -> List<&2, Lex.Tok>:
  match gp:
    case GNone{}:
      []
    case GOne{}:
      [space(" ")]
    case GTwo{}:
      [space("  ")]
    case GLine{}:
      [newline()]
    case GDent{}:
      [newline(), space("  ")]
    case GKeep{sp}:
      [space(sp)]

# what a token that is no comment is to the layout by its kind alone
def role.kind(k: Lex.TokKind) -> Role:
  match k:
    case Lex.TOpen{}:
      RBracket{}
    case Lex.TClose{}:
      RClose{}
    case Lex.TComma{}:
      RSep{}
    case other:
      RWord{}

# what a token is to the layout, given wrap's motion for it
def role.act(act: Wrap.Act, k: Lex.TokKind) -> Role:
  match act:
    case Wrap.AOpen{}:
      ROpen{}
    case Wrap.AEnd{}:
      REnd{}
    case Wrap.AComma{}:
      RComma{}
    case other:
      role.kind(k)

# wrap's motion for a token, at its walk so far
def act_of(wk: Wrap.Walk, tok: Lex.Tok, glued: Bool) -> Wrap.Act:
  Wrap.Walk{mode, paren, bracket, brace, angle, _shut, _open, _on, _pline, _pend, _pcol, _spans} = wk
  Lex.Tok{k, tx, _l, _c} = tok
  Wrap.check.act(mode, k, tx, glued, paren, angle, brace, bracket)

# a token's kind
def kind_of(tok: Lex.Tok) -> Lex.TokKind:
  Lex.Tok{k, _t, _l, _c} = tok
  k

# is the kind a comment's?
def is_note(k: Lex.TokKind) -> Bool:
  match k:
    case Lex.TComment{}:
      True{}
    case other:
      False{}

# what a token is to the layout: a comment by its kind, any other by wrap's
# motion for it
def role.pick(note: Bool, wk: Wrap.Walk, +tok: Lex.Tok, glued: Bool) -> Role:
  match note:
    case True{}:
      RNote{}
    case False{}:
      role.act(act_of(wk, tok, glued), kind_of(tok))

# what a token is to the layout
def role(wk: Wrap.Walk, +tok: Lex.Tok, glued: Bool) -> Role:
  role.pick(is_note(kind_of(tok)), wk, tok, glued)

# what a token leaves for the one after it
def after(rl: Role) -> Prev:
  match rl:
    case ROpen{}:
      POpen{}
    case RComma{}:
      PComma{}
    case RNote{}:
      PNote{}
    case RBracket{}:
      PBracket{}
    case RSep{}:
      PSep{}
    case other:
      PWord{}

# is the walk inside the parameter list?
def listing(ph: Wrap.Phase) -> Bool:
  match ph:
    case Wrap.Args{}:
      True{}
    case other:
      False{}

# the spaces that were there, or nothing where a line broke
def kept(brk: Bool, sp: String) -> Gap:
  match brk:
    case True{}:
      GNone{}
    case False{}:
      GKeep{sp}

# the spaces that were there, or one where a line broke
def joined(brk: Bool, sp: String) -> Gap:
  match brk:
    case True{}:
      GOne{}
    case False{}:
      GKeep{sp}

# a comment after the list's `(` or a comma: on that line, two spaces off,
# or on its own when a line broke before it
def noted(brk: Bool) -> Gap:
  match brk:
    case True{}:
      GDent{}
    case False{}:
      GTwo{}

# a line of its own: indented inside the parameter list, not outside it
def lined(inside: Bool) -> Gap:
  match inside:
    case True{}:
      GDent{}
    case False{}:
      GLine{}

# the gap before a token right after the list's `(`
def gap.open(rl: Role, brk: Bool) -> Gap:
  match rl:
    case REnd{}:
      GNone{}
    case RNote{}:
      noted(brk)
    case other:
      GDent{}

# the gap before a token right after a comma between parameters
def gap.comma(rl: Role, brk: Bool) -> Gap:
  match rl:
    case REnd{}:
      GLine{}
    case RNote{}:
      noted(brk)
    case other:
      GDent{}

# the gap before a token right after a comment
def gap.note(rl: Role, inside: Bool) -> Gap:
  match rl:
    case REnd{}:
      GLine{}
    case other:
      lined(inside)

# the gap before a token right after another opening bracket
def gap.bracket(rl: Role, brk: Bool, sp: String) -> Gap:
  match rl:
    case REnd{}:
      GLine{}
    case other:
      kept(brk, sp)

# a comment in the middle of a parameter: where it was on its line, or on a
# line of its own when a line broke before it
def gap.aside(brk: Bool, sp: String) -> Gap:
  match brk:
    case True{}:
      GDent{}
    case False{}:
      GKeep{sp}

# the gap before a token after anything else
def gap.word(rl: Role, brk: Bool, sp: String) -> Gap:
  match rl:
    case REnd{}:
      GLine{}
    case RNote{}:
      gap.aside(brk, sp)
    case RWord{}:
      joined(brk, sp)
    case other:
      kept(brk, sp)

# the gap before a token right after a comma inside a parameter: where a
# line broke, one space, so the comma keeps the space `bolt fmt` gives every
# comma; none before a closing bracket or another comma
def gap.sep(rl: Role, brk: Bool, sp: String) -> Gap:
  match rl:
    case REnd{}:
      GLine{}
    case RNote{}:
      gap.aside(brk, sp)
    case RClose{}:
      kept(brk, sp)
    case RSep{}:
      kept(brk, sp)
    case other:
      joined(brk, sp)

# the gap before a token: by what came before it, what it is, whether a line
# broke between them, the spaces between them, and whether the parameter
# list is open
def gap(pv: Prev, rl: Role, brk: Bool, sp: String, inside: Bool) -> Gap:
  match pv:
    case POpen{}:
      gap.open(rl, brk)
    case PComma{}:
      gap.comma(rl, brk)
    case PNote{}:
      gap.note(rl, inside)
    case PBracket{}:
      gap.bracket(rl, brk, sp)
    case PSep{}:
      gap.sep(rl, brk, sp)
    case PWord{}:
      gap.word(rl, brk, sp)

# the bracket depth after a token
def depth.after(k: Lex.TokKind, +depth: U32) -> U32:
  match k:
    case Lex.TOpen{}:
      (depth + 1 : U32)
    case Lex.TClose{}:
      Wrap.check.dec_u(depth)
    case other:
      depth

# is the token the `:` that ends a header: a colon outside every bracket?
def ends(k: Lex.TokKind, depth: U32) -> Bool:
  match k:
    case Lex.TColon{}:
      U32.is_eq(depth, 0)
    case other:
      False{}

# does the header these tokens go on with need rewriting: it reaches its
# `:`, and before that it breaks across lines, or is wider than 120 with
# the `def` before it (wide so far)? A `def` at column 0 before the `:`, or
# the tokens ending, means there is no header to read
def needs(toks: List<&2, Lex.Tok>, +depth: U32, +wide: U32, +brk: Bool) -> Bool:
  match toks:
    case Nil{}:
      False{}
    case Con{Lex.Tok{Lex.TNewline{}, _t, _l, _c}, rest}:
      needs(rest, depth, wide, True{})
    case Con{Lex.Tok{+k, +t, _l, _c}, rest}:
      +more = Wrap.check.add(wide, k, t)
      Lazy.either(Bool, ends(k, depth), _u => Bool.or(brk, U32.is_gt(more, 120)),
        _v => needs(rest, depth.after(k, depth), more, brk))

# is the token a `def` at column 0?
def starts(tok: Lex.Tok) -> Bool:
  match tok:
    case Lex.Tok{Lex.TKey{}, t, _l, c}:
      Bool.and(U32.is_eq(c, 0), String.eq(t, "def"))
    case other:
      False{}

# the state inside a header, its `def` just read
def entered(+tok: Lex.Tok) -> State:
  In{Wrap.check.step(tok, Wrap.check.start(), False{}), Wrap.check.glue_of(tok), PWord{}, False{}, "", 0}

# the state after a token outside a header: inside one when the token is a
# `def` whose header needs rewriting
def enter(+tok: Lex.Tok, rest: List<&2, Lex.Tok>) -> State:
  Lazy.either(State, Lazy.and_then(starts(tok), _u => needs(rest, 0, 3, False{})), _v => entered(tok), _w => Out{})

# the state after a token inside a header: outside again once it was the
# header's `:`
def leave(
  done: Bool,
  +wk: Wrap.Walk,
  +glued: Bool,
  +tok: Lex.Tok,
  depth: U32
) -> State:
  match done:
    case True{}:
      Out{}
    case False{}:
      In{Wrap.check.step(tok, wk, glued), Wrap.check.glue_of(tok), after(role(wk, tok, glued)), False{}, "",
        depth.after(kind_of(tok), depth)}

# the state after a token that is no space and no newline
def on_mark(st: State, +tok: Lex.Tok, rest: List<&2, Lex.Tok>) -> State:
  match st:
    case Out{}:
      enter(tok, rest)
    case In{wk, glued, _pv, _brk, _sp, +depth}:
      leave(ends(kind_of(tok), depth), wk, glued, tok, depth)

# the state after a space: inside a header it is remembered, not written
def on_space(st: State, text: String) -> State:
  match st:
    case Out{}:
      Out{}
    case In{wk, _glued, pv, brk, _sp, depth}:
      In{wk, False{}, pv, brk, text, depth}

# the state after a newline: inside a header a line broke
def on_line(st: State) -> State:
  match st:
    case Out{}:
      Out{}
    case In{wk, _glued, pv, _brk, _sp, depth}:
      In{wk, False{}, pv, True{}, "", depth}

# a space or a newline before the rest: written as it is outside a header,
# and dropped inside one, where the gap before the next token takes its
# place
def blank(st: State, tok: Lex.Tok, more: List<&2, Lex.Tok>) -> List<&2, Lex.Tok>:
  match st:
    case Out{}:
      tok <> more
    case In{_wk, _glued, _pv, _brk, _sp, _depth}:
      more

# the gap written before a token that is no space and no newline: none
# outside a header
def gap_at(st: State, tok: Lex.Tok) -> Gap:
  match st:
    case Out{}:
      GNone{}
    case In{+wk, glued, pv, brk, sp, _depth}:
      gap(pv, role(wk, tok, glued), brk, sp, listing(Wrap.check.mode_of(wk)))

# every header that needs it rewritten, the rest of the tokens as they were
def heads.go(toks: List<&2, Lex.Tok>, +st: State) -> List<&2, Lex.Tok>:
  match toks:
    case Nil{}:
      Nil{}
    case Con{Lex.Tok{Lex.TSpace{}, +t, l, c}, rest}:
      blank(st, Lex.Tok{Lex.TSpace{}, t, l, c}, heads.go(rest, on_space(st, t)))
    case Con{Lex.Tok{Lex.TNewline{}, t, l, c}, rest}:
      blank(st, Lex.Tok{Lex.TNewline{}, t, l, c}, heads.go(rest, on_line(st)))
    case Con{+tok, +rest}:
      List.append(&2, Lex.Tok, gap.toks(gap_at(st, tok)), tok <> heads.go(rest, on_mark(st, tok, rest)))

# a file's tokens with each def header that breaks, or is too wide, in the
# shape `wrap` asks for
def heads(toks: List<&2, Lex.Tok>) -> List<&2, Lex.Tok>:
  heads.go(toks, Out{})
