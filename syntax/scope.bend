# syntax/scope: the parameters and locals visible at a line of a source, and
# where each was bound. It works on tokens and indentation, not on an
# expression tree, so it holds up in a half-written def:
#   - the enclosing item is the last column-0 `def`, `law`, .. at or above;
#   - a def's parameters are the names at paren depth 1 of its header, which
#     runs to the first `:` at depth 0 (so it may span lines);
#   - in the body, a line binds names by its shape: `case pats:`, `for x: T`,
#     `lhs = v`, `x : T <- m`, `x : T = v`, and `x => e`;
#   - a block is its indentation: a `case` or a lambda binds for the deeper
#     lines below it, a let for the rest of its own block.
# It knows names and binding sites, not types: a local's note is the line
# that bound it (a parameter's is its own declaration, `+x: U32`).
import Base
import ./lex.bend as Lex

type Local is Data:
  Local{name: String, line: U32, col: U32, note: String, param: Bool}

# a line's significant tokens; indent is the first one's column
type Line is Data:
  Line{n: U32, indent: U32, toks: List<&2, Lex.Tok>}

# lines
# -----

type LS is Data:
  LS{cur: List<&2, Lex.Tok>, out: List<&2, Line>}

def line.make(toks: List<&2, Lex.Tok>, out: List<&2, Line>) -> List<&2, Line>:
  match toks:
    case Nil{}:
      out
    case Con{Lex.Tok{k, t, +l, +c}, rest}:
      Line{l, c, Lex.Tok{k, t, l, c} <> rest} <> out

def lines.step(tok: Lex.Tok, st: LS) -> LS:
  match tok:
    case Lex.Tok{Lex.TNewline{}, t, l, c}:
      LS{cur, out} = st
      LS{[], line.make(List.reverse(&2, Lex.Tok, cur), out)}
    case Lex.Tok{+k, t, l, c}:
      LS{+cur, out} = st
      LS{Bool.pick(List<&2, Lex.Tok>, Lex.significant(k), Lex.Tok{k, t, l, c} <> cur, cur), out}

def lines.run(toks: List<&2, Lex.Tok>, st: LS) -> LS:
  match toks:
    case Nil{}:
      st
    case Con{tok, t}:
      lines.run(t, lines.step(tok, st))

def lines.end(st: LS) -> List<&2, Line>:
  LS{cur, out} = st
  List.reverse(&2, Line, line.make(List.reverse(&2, Lex.Tok, cur), out))

def lines(source: String) -> List<&2, Line>:
  lines.end(lines.run(Lex.tokens(source), LS{[], []}))

# the enclosing item
# ------------------

def first_text(toks: List<&2, Lex.Tok>) -> String:
  match toks:
    case Nil{}:
      ""
    case Con{Lex.Tok{k, t, l, c}, rest}:
      t

def starts_item(+t: String) -> Bool:
  Bool.or(Bool.or(String.eq(t, "def"), String.eq(t, "law")),
    Bool.or(Bool.or(String.eq(t, "type"), String.eq(t, "import")), String.eq(t, "@")))

# the line of the last item start at or above qline
def start(ls: List<&2, Line>, +qline: U32, best: Maybe<&2, U32>) -> Maybe<&2, U32>:
  match ls:
    case Nil{}:
      best
    case Con{Line{+n, indent, toks}, t}:
      start(t, qline, Bool.pick(Maybe<&2, U32>,
        Bool.and(Bool.and(U32.is_le(n, qline), U32.is_eq(indent, 0)), starts_item(first_text(toks))),
        Some{n}, best))

# the lines from lo through hi
def within(ls: List<&2, Line>, +lo: U32, +hi: U32) -> List<&2, Line>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{Line{+n, indent, toks}, t}:
      +rest = within(t, lo, hi)
      Bool.pick(List<&2, Line>, Bool.and(U32.is_ge(n, lo), U32.is_le(n, hi)), Line{n, indent, toks} <> rest, rest)

def flat(ls: List<&2, Line>) -> List<&2, Lex.Tok>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{Line{n, indent, toks}, t}:
      List.append(&2, Lex.Tok, toks, flat(t))

# token helpers
# -------------

def is_open(k: Lex.TokKind) -> Bool:
  match k:
    case Lex.TOpen{}:
      True{}
    case other:
      False{}

def is_close(k: Lex.TokKind) -> Bool:
  match k:
    case Lex.TClose{}:
      True{}
    case other:
      False{}

def is_comma(k: Lex.TokKind) -> Bool:
  match k:
    case Lex.TComma{}:
      True{}
    case other:
      False{}

def is_name(k: Lex.TokKind) -> Bool:
  match k:
    case Lex.TName{}:
      True{}
    case other:
      False{}

def lower_first(cs: List<&2, Char>) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case Con{+c, t}:
      Bool.or(Char.is_lower(c), Char.is_eq(c, '_'))

# a name a pattern can bind: lowercase, undotted, not `_`
def binds(+t: String) -> Bool:
  Bool.and(lower_first(String.to_list(t)), Bool.and(Bool.not(String.contains(t, ".")), Bool.not(String.eq(t, "_"))))

def depth_after(+k: Lex.TokKind, +d: U32) -> U32:
  Bool.pick(U32, is_open(k), (d + 1 : U32),
    Bool.pick(U32, Bool.and(is_close(k), U32.is_gt(d, 0)), (d - 1 : U32), d))

# a declaration's tokens as text: `+x: U32`, `~f: U32 -> U32`
def render(toks: List<&2, Lex.Tok>) -> String:
  match toks:
    case Nil{}:
      ""
    case Con{Lex.Tok{k, +t, l, c}, rest}:
      Bool.pick(String, String.eq(t, "->"), " -> ",
        Bool.pick(String, Bool.or(String.eq(t, ":"), String.eq(t, ",")), t ++ " ", t)) ++ render(rest)

# parameters
# ----------

# done: the header's closing `:` was seen (on line endl); closed: the parameter
# list ended, so a later `(` is the return type's (`-> IO(Unit)`); angle: the
# depth inside `<..>`, where a comma separates type arguments, not parameters;
# pend: the tokens of the parameter being read; pend and out are reversed
type PS is Data:
  PS{done: Bool, closed: Bool, depth: U32, angle: U32, endl: U32, pend: List<&2, Lex.Tok>, out: List<&2, Local>}

# `<` and `<&` open type arguments; `<-` and `<>` are operators
def angle_after(+t: String, +a: U32) -> U32:
  Bool.pick(U32, Bool.and(String.starts_with(t, "<"), Bool.not(Bool.or(String.eq(t, "<-"), String.eq(t, "<>")))),
    (a + 1 : U32), Bool.pick(U32, Bool.and(String.eq(t, ">"), U32.is_gt(a, 0)), (a - 1 : U32), a))

def first_name(toks: List<&2, Lex.Tok>) -> Maybe<&2, Lex.Tok>:
  match toks:
    case Nil{}:
      None{}
    case Con{Lex.Tok{+k, t, l, c}, rest}:
      +more = first_name(rest)
      Bool.pick(Maybe<&2, Lex.Tok>, is_name(k), Some{Lex.Tok{k, t, l, c}}, more)

def param.of(name: Maybe<&2, Lex.Tok>, +toks: List<&2, Lex.Tok>, out: List<&2, Local>) -> List<&2, Local>:
  match name:
    case None{}:
      out
    case Some{Lex.Tok{k, t, l, c}}:
      Local{t, l, c, render(toks), True{}} <> out

def param(pend: List<&2, Lex.Tok>, out: List<&2, Local>) -> List<&2, Local>:
  +toks = List.reverse(&2, Lex.Tok, pend)
  param.of(first_name(toks), toks, out)

def params.step(tok: Lex.Tok, st: PS) -> PS:
  Lex.Tok{+k, +t, +l, +c} = tok
  PS{+done, +closed, +depth, +angle, +endl, +pend, +out} = st
  +at1 = Bool.and(U32.is_eq(depth, 1), Bool.not(closed))
  +last = Bool.and(at1, is_close(k))
  +ends = Bool.or(last, Bool.and(Bool.and(at1, U32.is_eq(angle, 0)), is_comma(k)))
  +opens = Bool.and(U32.is_eq(depth, 0), is_open(k))
  +closes = Bool.and(U32.is_eq(depth, 0), String.eq(t, ":"))
  Bool.pick(PS, done, PS{True{}, closed, depth, angle, endl, pend, out},
    PS{closes, Bool.or(closed, last), depth_after(k, depth), angle_after(t, angle), Bool.pick(U32, closes, l, endl),
      Bool.pick(List<&2, Lex.Tok>, Bool.or(ends, opens), [],
        Bool.pick(List<&2, Lex.Tok>, Bool.and(U32.is_ge(depth, 1), Bool.not(closed)), Lex.Tok{k, t, l, c} <> pend, pend)),
      Bool.pick(List<&2, Local>, ends, param(pend, out), out)})

def params.run(toks: List<&2, Lex.Tok>, st: PS) -> PS:
  match toks:
    case Nil{}:
      st
    case Con{tok, t}:
      params.run(t, params.step(tok, st))

# body lines
# ----------

# the names a pattern binds: a name followed by an opening bracket is a
# constructor or a call, not a binder
def names(toks: List<&2, Lex.Tok>, +note: String) -> List<&2, Local>:
  match toks:
    case Nil{}:
      Nil{}
    case Con{Lex.Tok{Lex.TName{}, t, l, c}, Con{Lex.Tok{Lex.TOpen{}, ot, ol, oc}, rest}}:
      names(rest, note)
    case Con{Lex.Tok{Lex.TName{}, +t, l, c}, rest}:
      +more = names(rest, note)
      Bool.pick(List<&2, Local>, binds(t), Local{t, l, c, note, False{}} <> more, more)
    case Con{other, rest}:
      names(rest, note)

# a typed binder's tokens stop at its `:`
def before_colon(toks: List<&2, Lex.Tok>) -> List<&2, Lex.Tok>:
  match toks:
    case Nil{}:
      Nil{}
    case Con{Lex.Tok{k, +t, l, c}, rest}:
      +more = before_colon(rest)
      Bool.pick(List<&2, Lex.Tok>, String.eq(t, ":"), [], Lex.Tok{k, t, l, c} <> more)

# hit: a `=` or `<-` at depth 0 was seen; lhs: the tokens before it; lams: the
# names right before a `=>`; prev: the last token
type LB is Data:
  LB{depth: U32, hit: Bool, lhs: List<&2, Lex.Tok>, lams: List<&2, Local>, prev: Lex.Tok}

def lam(prev: Lex.Tok, +note: String, +lams: List<&2, Local>) -> List<&2, Local>:
  Lex.Tok{k, +t, l, c} = prev
  Bool.pick(List<&2, Local>, Bool.and(is_name(k), binds(t)), Local{t, l, c, note, False{}} <> lams, lams)

def scan.step(tok: Lex.Tok, st: LB, +note: String) -> LB:
  Lex.Tok{+k, +t, +l, +c} = tok
  LB{+depth, +hit, +lhs, +lams, prev} = st
  +bind = Bool.and(Bool.and(U32.is_eq(depth, 0), Bool.not(hit)), Bool.or(String.eq(t, "="), String.eq(t, "<-")))
  LB{depth_after(k, depth), Bool.or(hit, bind),
    Bool.pick(List<&2, Lex.Tok>, Bool.or(hit, bind), lhs, Lex.Tok{k, t, l, c} <> lhs),
    Bool.pick(List<&2, Local>, String.eq(t, "=>"), lam(prev, note, lams), lams),
    Lex.Tok{k, t, l, c}}

def scan.run(toks: List<&2, Lex.Tok>, st: LB, +note: String) -> LB:
  match toks:
    case Nil{}:
      st
    case Con{tok, t}:
      scan.run(t, scan.step(tok, st, note), note)

# what a line binds for the rest of its own block (lets), and for the deeper
# lines below it (heads)
type Binds is Data:
  Binds{lets: List<&2, Local>, heads: List<&2, Local>}

def binders.of(+first: String, +toks: List<&2, Lex.Tok>, scanned: LB, +note: String) -> Binds:
  LB{depth, hit, lhs, lams, prev} = scanned
  Bool.pick(Binds, String.eq(first, "case"), Binds{[], names(List.tail(&2, Lex.Tok, toks), note)},
    Bool.pick(Binds, Bool.or(String.eq(first, "for"), String.eq(first, "exs")),
      Binds{names(before_colon(List.tail(&2, Lex.Tok, toks)), note), []},
      Binds{Bool.pick(List<&2, Local>, hit, names(before_colon(List.reverse(&2, Lex.Tok, lhs)), note), []), lams}))

def binders(+toks: List<&2, Lex.Tok>, +note: String) -> Binds:
  binders.of(first_text(toks), toks, scan.run(toks, LB{0, False{}, [], [], Lex.Tok{Lex.TSpace{}, "", 0, 0}}, note), note)

# a frame's locals are visible on lines indented at least `threshold`
type Frame is Data:
  Frame{threshold: U32, locals: List<&2, Local>}

def pop(frames: List<&2, Frame>, +indent: U32) -> List<&2, Frame>:
  match frames:
    case Nil{}:
      Nil{}
    case Con{Frame{+th, locals}, rest}:
      +below = pop(rest, indent)
      Bool.pick(List<&2, Frame>, U32.is_lt(indent, th), below, Frame{th, locals} <> below)

def push(+locals: List<&2, Local>, threshold: U32, +frames: List<&2, Frame>) -> List<&2, Frame>:
  Bool.pick(List<&2, Frame>, List.is_empty(&2, Local, locals), frames, Frame{threshold, locals} <> frames)

def lstrip.go(cs: List<&2, Char>) -> List<&2, Char>:
  match cs:
    case Con{' ', t}:
      lstrip.go(t)
    case other:
      other

def note_of(src: List<&2, String>, n: U32) -> String:
  String.from_list(lstrip.go(String.to_list(Maybe.default(&2, String, List.get(&2, String, src, U32.to_nat(n)), ""))))

def body.line(b: Binds, +indent: U32, frames: List<&2, Frame>) -> List<&2, Frame>:
  Binds{lets, heads} = b
  push(heads, (indent + 1 : U32), push(lets, indent, pop(frames, indent)))

def body(ls: List<&2, Line>, +src: List<&2, String>, frames: List<&2, Frame>) -> List<&2, Frame>:
  match ls:
    case Nil{}:
      frames
    case Con{Line{n, indent, toks}, t}:
      body(t, src, body.line(binders(toks, note_of(src, n)), indent, frames))

def locals_of(frames: List<&2, Frame>) -> List<&2, Local>:
  match frames:
    case Nil{}:
      Nil{}
    case Con{Frame{th, locals}, rest}:
      List.append(&2, Local, locals, locals_of(rest))

# putting it together
# -------------------

def item.body(ps: PS, +first: String, ls: List<&2, Line>, src: List<&2, String>, +qline: U32) -> List<&2, Local>:
  PS{done, closed, depth, angle, +endl, pend, out} = ps
  Bool.pick(List<&2, Local>, Bool.or(Bool.or(String.eq(first, "def"), String.eq(first, "@")), String.eq(first, "law")),
    List.append(&2, Local, locals_of(body(within(ls, (endl + 1 : U32), qline), src, [])),
      List.reverse(&2, Local, out)),
    [])

# a def's parameters, then its body's frames, from the item's lines
def item(+first: String, +ls: List<&2, Line>, +src: List<&2, String>, +from: U32, +qline: U32) -> List<&2, Local>:
  +ps = params.run(flat(ls), PS{Bool.not(Bool.or(String.eq(first, "def"), String.eq(first, "@"))), False{}, 0, 0, from, [], []})
  item.body(ps, first, ls, src, qline)

def visible.from(m: Maybe<&2, U32>, +ls: List<&2, Line>, src: List<&2, String>, +qline: U32) -> List<&2, Local>:
  match m:
    case None{}:
      Nil{}
    case Some{+from}:
      item(first_text(flat(within(ls, from, from))), within(ls, from, qline), src, from, qline)

# the parameters and locals visible at a line, innermost first
def visible(+source: String, +qline: U32) -> List<&2, Local>:
  +ls = lines(source)
  visible.from(start(ls, qline, None{}), ls, String.lines(source), qline)

def lookup.in(ls: List<&2, Local>, +name: String) -> Maybe<&2, Local>:
  match ls:
    case Nil{}:
      None{}
    case Con{Local{+n, l, c, note, p}, t}:
      +more = lookup.in(t, name)
      Bool.pick(Maybe<&2, Local>, String.eq(n, name), Some{Local{n, l, c, note, p}}, more)

# the binding a name refers to at a line
def lookup(source: String, line: U32, name: String) -> Maybe<&2, Local>:
  lookup.in(visible(source, line), name)
