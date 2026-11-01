# `wrap` reports exactly one finding for each def header that breaks its shape
# and none otherwise: a one-line header wider than 120 columns through its
# last `:` (the whole header when it has none), counted as `space` counts a
# line except that a comment counts zero, or a header across lines (one
# holding a newline token; a line break inside a string literal does not
# count) whose parameter list (opened by the first `(` with no bracket open,
# split by the commas at its own depth) holds a parameter that spans lines,
# starts on the `(` line, or starts on the line a later parameter starts on,
# or holds no parameter at all, or closes with its `)` not on a line below the
# last parameter's last line, or with no `->` (or, with no return type, the
# header's `:`) right after its `)` on the `)` line.
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/syntax/bind.bend as Bind
import ../src/rules/style/space.bend as Space
import ../src/src.bend as Src
import ../src/syntax/tree.bend as Tree
import ../src/syntax/outline.bend as Outline
import ../src/rules/style/wrap.bend as Wrap
import ../src/lazy/lazy.bend as Lazy

# The header rule wrap (laws/WrapReportsBrokenHeaderShape.bend) judges each def header of the
# outline by its sig's tokens (Lex.tokens), once: a finding or none. A
# header is across lines when one of its tokens is a newline (Lex.is_nl), so
# a line break inside a string literal does not count. A header on one line
# is too wide past 120 columns, measured through its last `:` (the whole
# header when it has none), a comment counting none and every other token
# counted the way space counts it (Space.width_of: a string literal two, any
# other token its length). A header across lines is judged by its parameter
# list. The list opens at the first `(` read while no bracket is open. Inside
# it, with only that `(` open, a `)` ends the list and a `,` ends a
# parameter; every other significant token is part of a parameter. A
# parameter is misplaced when it spans lines, starts on the `(` line, or
# starts on the line a later parameter starts on; the list is empty when it
# opened and holds no parameter; it is cramped when it closed and its `)` is
# not on a line below the last parameter's last line; it is loose when it
# closed and the next significant token is not a `->` (or the `:` of a
# header with no return type) on the `)` line. The spec reads single tokens
# with the rule's own readings and no more: Wrap.check.is_colon (a `:`),
# Wrap.check.is_arrow (a `->`), Wrap.check.is_oparen and Wrap.check.is_cparen
# (the text `(`, `)`), Lex.is_comma, Lex.significant, Lex.is_name (a name
# glues a `<` right after it), Wrap.check.brackets (the bracket a token opens
# or closes: `(` `[` `{` and `)` `]` `}`, a `<` or `<&` glued to a name
# opening an angle, a run of `>` closing) and Wrap.check.ticks_of (how many
# angles that run closes).

# a comment?
def wrap.comment(kk: Lex.TokKind) -> Bool:
  match kk:
    case Lex.TComment{}:
      True{}
    case other:
      False{}

# a token's share of a one-line header's width: none for a comment, else its
# share of a line as space counts it
def wrap.cost(+kk: Lex.TokKind, +tx: String) -> U32:
  Bool.pick(U32, wrap.comment(kk), 0, Space.width_of(kk, tx))

# some token of the list is a `:`
def wrap.colons(toks: List<&2, Lex.Tok>) -> Bool:
  match toks:
    case Nil{}:
      False{}
    case Con{Lex.Tok{kk, tx, ln, cl}, rest}:
      Bool.or(Wrap.check.is_colon(kk), wrap.colons(rest))

# the width, acc so far, through the last `:` of the tokens
def wrap.upto(toks: List<&2, Lex.Tok>, +acc: U32) -> U32:
  match toks:
    case Nil{}:
      acc
    case Con{Lex.Tok{+kk, +tx, ln, cl}, +rest}:
      +next = (acc + wrap.cost(kk, tx) : U32)
      Bool.pick(U32, wrap.colons(rest), wrap.upto(rest, next), next)

# the width of all the tokens, acc so far
def wrap.total(toks: List<&2, Lex.Tok>, +acc: U32) -> U32:
  match toks:
    case Nil{}:
      acc
    case Con{Lex.Tok{+kk, +tx, ln, cl}, rest}:
      wrap.total(rest, (acc + wrap.cost(kk, tx) : U32))

# a one-line header's width: through its last `:`, else all of it
def wrap.width(+toks: List<&2, Lex.Tok>) -> U32:
  Bool.pick(U32, wrap.colons(toks), wrap.upto(toks, 0), wrap.total(toks, 0))

# LAW: wrap measures a header through its last `:`, the whole header when it
# has none, a string literal two columns and a comment none
law wrap_width:
  for +toks: List<&2, Lex.Tok>
  {Wrap.check.width.go(toks, 0, 0, False{}) == wrap.width(toks) : U32}

# a broken header read so far: where it stands (before its parameter list,
# inside it, just past its `)`, past a `->` on the `)` line, past anything
# else), the paren, bracket, brace and angle depths, the
# `(` line, the `)` line, the parameter being read, and those read, last first
type wrap.Read is Data:
  wrap.Read{at: Wrap.Phase, paren: U32, bracket: U32, brace: U32, angle: U32, open: U32, shut: U32,
    cur: Maybe<&2, Wrap.Span>, done: List<&2, Wrap.Span>}

# nothing read yet
def wrap.start() -> wrap.Read:
  wrap.Read{Wrap.Seek{}, 0, 0, 0, 0, 0, 0, None{}, []}

# no depth open
def wrap.shut_all(+paren: U32, +bracket: U32, +brace: U32, +angle: U32) -> Bool:
  Bool.and(U32.is_eq(paren, 0), Bool.and(U32.is_eq(angle, 0), Bool.and(U32.is_eq(brace, 0), U32.is_eq(bracket, 0))))

# only the list's own `(` open
def wrap.flat(+paren: U32, +bracket: U32, +brace: U32, +angle: U32) -> Bool:
  Bool.and(U32.is_eq(paren, 1), Bool.and(U32.is_eq(angle, 0), Bool.and(U32.is_eq(brace, 0), U32.is_eq(bracket, 0))))

# at the list's own depth: a `)` ends the list, a `,` a parameter, and any
# other token moves as it would anywhere
def wrap.edge(+kk: Lex.TokKind, +tx: String, move: Wrap.Act) -> Wrap.Act:
  Bool.pick(Wrap.Act, Wrap.check.is_cparen(kk, tx), Wrap.AEnd{},
    Bool.pick(Wrap.Act, Lex.is_comma(kk), Wrap.AComma{}, move))

# what a significant token does. Before the list a `(` with no depth open
# opens it; inside it, with only its `(` open, a `)` or a `,` is an edge;
# right after its `)` a token is a `->` (or a `:`) or a stray; later nothing
# moves; any other token moves the depths as Wrap.check.brackets reads it
def wrap.motion(
  at: Wrap.Phase,
  +kk: Lex.TokKind,
  +tx: String,
  +glued: Bool,
  +paren: U32,
  +bracket: U32,
  +brace: U32,
  +angle: U32
) -> Wrap.Act:
  match at:
    case Wrap.Seek{}:
      Bool.pick(Wrap.Act, Bool.and(Wrap.check.is_oparen(kk, tx), wrap.shut_all(paren, bracket, brace, angle)),
        Wrap.AOpen{}, Wrap.check.brackets(kk, tx, glued))
    case Wrap.Args{}:
      Bool.pick(Wrap.Act, wrap.flat(paren, bracket, brace, angle),
        wrap.edge(kk, tx, Wrap.check.brackets(kk, tx, glued)), Wrap.check.brackets(kk, tx, glued))
    case Wrap.Past{}:
      Wrap.ANone{}
    case Wrap.Shut{}:
      Bool.pick(Wrap.Act, Bool.or(Wrap.check.is_arrow(kk), Wrap.check.is_colon(kk)), Wrap.AArrow{}, Wrap.AStray{})
    case Wrap.Loose{}:
      Wrap.ANone{}

# one less, not below zero
def wrap.less(+nn: U32) -> U32:
  Lazy.stop(U32, U32.is_eq(nn, 0), 0, _u => (nn - 1 : U32))

# left angles closed, the depth staying at zero once there
def wrap.lower(left: Nat, +angle: U32) -> U32:
  match left:
    case Zero{}:
      angle
    case Succ{p}:
      Bool.pick(U32, U32.is_eq(angle, 0), angle, wrap.lower(p, (angle - 1 : U32)))

# the parameter being read, taken on to this token
def wrap.extend(cur: Maybe<&2, Wrap.Span>, +ln: U32, +cl: U32) -> Maybe<&2, Wrap.Span>:
  match cur:
    case None{}:
      Some{Wrap.Span{ln, ln, cl}}
    case Some{Wrap.Span{line, _end, col}}:
      Some{Wrap.Span{line, ln, col}}

# the parameter being read, onto those read
def wrap.close(cur: Maybe<&2, Wrap.Span>, done: List<&2, Wrap.Span>) -> List<&2, Wrap.Span>:
  match cur:
    case None{}:
      done
    case Some{sp}:
      sp <> done

# new depths; inside the list the token joins the parameter being read
def wrap.join(
  at: Wrap.Phase,
  paren: U32,
  bracket: U32,
  brace: U32,
  angle: U32,
  open: U32,
  shut: U32,
  cur: Maybe<&2, Wrap.Span>,
  done: List<&2, Wrap.Span>,
  +ln: U32,
  +cl: U32
) -> wrap.Read:
  match at:
    case Wrap.Args{}:
      wrap.Read{Wrap.Args{}, paren, bracket, brace, angle, open, shut, wrap.extend(cur, ln, cl), done}
    case Wrap.Seek{}:
      wrap.Read{Wrap.Seek{}, paren, bracket, brace, angle, open, shut, cur, done}
    case Wrap.Past{}:
      wrap.Read{Wrap.Past{}, paren, bracket, brace, angle, open, shut, cur, done}
    case Wrap.Shut{}:
      wrap.Read{Wrap.Shut{}, paren, bracket, brace, angle, open, shut, cur, done}
    case Wrap.Loose{}:
      wrap.Read{Wrap.Loose{}, paren, bracket, brace, angle, open, shut, cur, done}

# past the `)`, a `->` on its line puts the return type there; on a later
# line it does not
def wrap.turn(+ln: U32, +shut: U32) -> Wrap.Phase:
  Bool.pick(Wrap.Phase, U32.is_eq(ln, shut), Wrap.Past{}, Wrap.Loose{})

# a significant token's motion applied to the read, the token on line ln at
# column cl, closing ticks angles if it closes any
def wrap.move(
  act: Wrap.Act,
  at: Wrap.Phase,
  +paren: U32,
  +bracket: U32,
  +brace: U32,
  +angle: U32,
  open: U32,
  +shut: U32,
  cur: Maybe<&2, Wrap.Span>,
  done: List<&2, Wrap.Span>,
  +ln: U32,
  +cl: U32,
  ticks: Nat
) -> wrap.Read:
  match act:
    case Wrap.AOpen{}:
      wrap.Read{Wrap.Args{}, 1, bracket, brace, angle, ln, 0, None{}, done}
    case Wrap.AEnd{}:
      wrap.Read{Wrap.Shut{}, wrap.less(paren), bracket, brace, angle, open, ln, None{}, wrap.close(cur, done)}
    case Wrap.AComma{}:
      wrap.Read{at, paren, bracket, brace, angle, open, shut, None{}, wrap.close(cur, done)}
    case Wrap.AArrow{}:
      wrap.Read{wrap.turn(ln, shut), paren, bracket, brace, angle, open, shut, cur, done}
    case Wrap.AStray{}:
      wrap.Read{Wrap.Loose{}, paren, bracket, brace, angle, open, shut, cur, done}
    case Wrap.AParen{}:
      wrap.join(at, (paren + 1 : U32), bracket, brace, angle, open, shut, cur, done, ln, cl)
    case Wrap.AUnparen{}:
      wrap.join(at, wrap.less(paren), bracket, brace, angle, open, shut, cur, done, ln, cl)
    case Wrap.ABrack{}:
      wrap.join(at, paren, (bracket + 1 : U32), brace, angle, open, shut, cur, done, ln, cl)
    case Wrap.AUnbrack{}:
      wrap.join(at, paren, wrap.less(bracket), brace, angle, open, shut, cur, done, ln, cl)
    case Wrap.ABrace{}:
      wrap.join(at, paren, bracket, (brace + 1 : U32), angle, open, shut, cur, done, ln, cl)
    case Wrap.AUnbrace{}:
      wrap.join(at, paren, bracket, wrap.less(brace), angle, open, shut, cur, done, ln, cl)
    case Wrap.AAngle{}:
      wrap.join(at, paren, bracket, brace, (angle + 1 : U32), open, shut, cur, done, ln, cl)
    case Wrap.AUnangle{}:
      wrap.join(at, paren, bracket, brace, wrap.lower(ticks, angle), open, shut, cur, done, ln, cl)
    case Wrap.ANone{}:
      wrap.join(at, paren, bracket, brace, angle, open, shut, cur, done, ln, cl)

# one token onto the read; a space, a newline or a comment changes nothing
def wrap.step(+tok: Lex.Tok, +rd: wrap.Read, glued: Bool) -> wrap.Read:
  Lex.Tok{+kk, +tx, +ln, +cl} = tok
  wrap.Read{+at, +paren, +bracket, +brace, +angle, +open, +shut, +cur, +done} = rd
  Bool.pick(wrap.Read, Lex.significant(kk),
    wrap.move(wrap.motion(at, kk, tx, glued, paren, bracket, brace, angle), at, paren, bracket, brace, angle, open,
      shut, cur, done, ln, cl, Wrap.check.ticks_of(tx)),
    wrap.Read{at, paren, bracket, brace, angle, open, shut, cur, done})

# the tokens read in order, each glued when the token before it is a name;
# at the end the parameter being read is done
def wrap.run(toks: List<&2, Lex.Tok>, rd: wrap.Read, glued: Bool) -> wrap.Read:
  match toks:
    case Nil{}:
      wrap.Read{at, paren, bracket, brace, angle, open, shut, cur, done} = rd
      wrap.Read{at, paren, bracket, brace, angle, open, shut, None{}, wrap.close(cur, done)}
    case Con{+tok, rest}:
      Lex.Tok{+kk, _tx, _ln, _cl} = tok
      wrap.run(rest, wrap.step(tok, rd, glued), Lex.is_name(kk))

# some parameter of the list starts on the line
def wrap.starts_on(ps: List<&2, Wrap.Span>, +ln: U32) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case Con{Wrap.Span{+line, _end, _col}, rest}:
      Bool.or(U32.is_eq(line, ln), wrap.starts_on(rest, ln))

# some parameter, in source order, spans lines, starts on the `(` line, or
# starts on the line a later one starts on
def wrap.misplaced(ps: List<&2, Wrap.Span>, +open: U32) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case Con{Wrap.Span{+line, +end, _col}, +rest}:
      Bool.or(Bool.or(Bool.not(U32.is_eq(line, end)), Bool.or(U32.is_eq(line, open), wrap.starts_on(rest, line))),
        wrap.misplaced(rest, open))

# the last parameter (the first of those read, last first) does not end on a
# line above the `)` line
def wrap.tight(ps: List<&2, Wrap.Span>, +shut: U32) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case Con{Wrap.Span{_line, +end, _col}, _rest}:
      Bool.not(U32.is_lt(end, shut))

# the list closed, and its `)` is not on a line below the last parameter's
def wrap.cramped(at: Wrap.Phase, +shut: U32, done: List<&2, Wrap.Span>) -> Bool:
  match at:
    case Wrap.Past{}:
      wrap.tight(done, shut)
    case Wrap.Shut{}:
      wrap.tight(done, shut)
    case Wrap.Loose{}:
      wrap.tight(done, shut)
    case Wrap.Seek{}:
      False{}
    case Wrap.Args{}:
      False{}

# no parameter read
def wrap.none(done: List<&2, Wrap.Span>) -> Bool:
  match done:
    case Nil{}:
      True{}
    case Con{_sp, _rest}:
      False{}

# the list opened and holds no parameter
def wrap.empty(at: Wrap.Phase, done: List<&2, Wrap.Span>) -> Bool:
  match at:
    case Wrap.Seek{}:
      False{}
    case Wrap.Args{}:
      wrap.none(done)
    case Wrap.Past{}:
      wrap.none(done)
    case Wrap.Shut{}:
      wrap.none(done)
    case Wrap.Loose{}:
      wrap.none(done)

# the list closed, and no `->` follows its `)` on the `)` line
def wrap.loose(at: Wrap.Phase) -> Bool:
  match at:
    case Wrap.Shut{}:
      True{}
    case Wrap.Loose{}:
      True{}
    case Wrap.Seek{}:
      False{}
    case Wrap.Args{}:
      False{}
    case Wrap.Past{}:
      False{}

# a header read to its end is misshapen: a parameter misplaced, or the list
# empty, cramped or loose
def wrap.bad_shape(rd: wrap.Read) -> Bool:
  wrap.Read{+at, _paren, _bracket, _brace, _angle, +open, +shut, _cur, +done} = rd
  Bool.or(wrap.misplaced(List.reverse(&2, Wrap.Span, done), open),
    Bool.or(wrap.empty(at, done), Bool.or(wrap.cramped(at, shut, done), wrap.loose(at))))

# a broken header's tokens are misshapen
def wrap.shape(toks: List<&2, Lex.Tok>) -> Bool:
  wrap.bad_shape(wrap.run(toks, wrap.start(), False{}))

# LAW: over the tokens of a broken header, wrap reports one finding when a
# parameter spans lines, starts on the `(` line or on another parameter's
# line, the list holds no parameter, or the list's `)` is not on a line below
# the last parameter or has no `->` (or `:`) right after it on its line, and
# none otherwise
law wrap_shape_counts:
  for toks: List<&2, Lex.Tok>
  for +line: U32
  for +path: String
  {List.length(&2, F.Finding, Wrap.check.jam(line, toks, path, [])) == Bool.pick(Nat, wrap.shape(toks), 1n, 0n) : Nat}

# some token of the list is a newline
def wrap.lines(toks: List<&2, Lex.Tok>) -> Bool:
  match toks:
    case Nil{}:
      False{}
    case Con{Lex.Tok{kk, tx, ln, cl}, rest}:
      Bool.or(Lex.is_nl(kk), wrap.lines(rest))

# a header is misshapen: across lines (a newline token in it) by its
# parameter list, on one line by a width over 120
def wrap.bad(+sig: String) -> Bool:
  Bool.pick(Bool, wrap.lines(Lex.tokens(sig)), wrap.shape(Lex.tokens(sig)), U32.is_gt(wrap.width(Lex.tokens(sig)), 120))

# how many items of the outline are def headers that are misshapen
def wrap.count(items: List<&2, Outline.Item>) -> Nat:
  match items:
    case Nil{}:
      0n
    case Con{Outline.Item{kk, _name, _line, +sig, _doc, _pp}, rest}:
      +m = wrap.count(rest)
      Bool.pick(Nat, Bool.and(Outline.is_def(kk), wrap.bad(sig)), 1n+m, m)

# LAW: wrap reports exactly one finding for each def header of the outline
# that is misshapen, and none for anything else
law wrap_counts:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Wrap.check(Src.Src{path, text, toks, tree, bound, items})) == wrap.count(items) : Nat}
