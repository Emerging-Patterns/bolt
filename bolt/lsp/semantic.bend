# lsp/semantic: every token of a document classified for the editor's
# semantic highlighting, from the lexer's kinds and the binder's resolution.
# A name's class comes from what it refers to: a parameter stays a parameter
# at every use, a constructor of this file is one wherever it appears. A name
# from elsewhere is read by its shape: `Bool.pick` a function, `U32` a type,
# `Nil{` a constructor.
import Base
import ../../syntax/lex.bend as Lex
import ../../syntax/bind.bend as Bind

# the legend, by index: keyword 0, function 1, type 2, enumMember 3,
# parameter 4, variable 5, property 6, string 7, number 8, comment 9,
# typeParameter 10
def legend() -> List<&2, String>:
  ["keyword", "function", "type", "enumMember", "parameter", "variable", "property", "string", "number",
   "comment", "typeParameter"]

# a classified token: where, how long, which type of the legend
type Sem is Data:
  Sem{line: U32, col: U32, len: U32, typ: U32}

# does the name start with a capital?
def upper_first(cs: List<&2, Char>) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case Con{c, t}:
      Char.is_upper(c)

# the last segment of a dotted name
def last_segment(cs: List<&2, Char>, +acc: List<&2, Char>) -> List<&2, Char>:
  match cs:
    case Nil{}:
      List.reverse(&2, Char, acc)
    case Con{'.', t}:
      last_segment(t, [])
    case Con{c, t}:
      last_segment(t, c <> acc)

# the legend's type for a binder of this kind (an item is a type when
# capitalized, else a function)
def of_kind(kk: Bind.BindKind, +name: String) -> U32:
  match kk:
    case Bind.KItem{}:
      Bool.pick(U32, upper_first(String.to_list(name)), 2, 1)
    case Bind.KCtor{}:
      3
    case Bind.KParam{}:
      4
    case Bind.KLocal{}:
      5
    case Bind.KPat{}:
      5
    case Bind.KFor{}:
      5
    case Bind.KField{}:
      6
    case Bind.KTypeParam{}:
      10
    case Bind.KTypeVar{}:
      10

# the type for a binder that may not have been found (a variable then)
def of_maybe_kind(mm: Maybe<&2, Bind.BindKind>, name: String) -> U32:
  match mm:
    case None{}:
      5
    case Some{k}:
      of_kind(k, name)

# a name from elsewhere: braced: a constructor; capitalized: a type; dotted:
# a function; else a variable
def by_shape(+name: String, braced: Bool) -> U32:
  Bool.pick(U32, upper_first(last_segment(String.to_list(name), [])), Bool.pick(U32, braced, 3, 2),
    Bool.pick(U32, String.contains(name, "."), 1, 5))

# the binders and uses are in source order, as the tokens are: each token
# takes the head of either list when it sits there, so a document classifies
# in one pass
type Cursor is Data:
  Cursor{binds: List<&2, Bind.Bind>, uses: List<&2, Bind.Use>}

# does the next binder sit at this position?
def at_head_bind(binds: List<&2, Bind.Bind>, +line: U32, +col: U32) -> Bool:
  match binds:
    case Nil{}:
      False{}
    case Con{Bind.Bind{n, l, c, k, note}, rest}:
      Bool.and(U32.is_eq(l, line), U32.is_eq(c, col))

# does the next use sit at this position?
def at_head_use(uses: List<&2, Bind.Use>, +line: U32, +col: U32) -> Bool:
  match uses:
    case Nil{}:
      False{}
    case Con{Bind.Use{n, l, c, tg}, rest}:
      Bool.and(U32.is_eq(l, line), U32.is_eq(c, col))

# a list's head is behind the token: it was never matched (a name the lexer
# and the binder disagree on); it is dropped so the rest can line up again
def behind_bind(binds: List<&2, Bind.Bind>, +line: U32, +col: U32) -> Bool:
  match binds:
    case Nil{}:
      False{}
    case Con{Bind.Bind{n, +l, c, k, note}, rest}:
      Bool.or(U32.is_lt(l, line), Bool.and(U32.is_eq(l, line), U32.is_lt(c, col)))

# is the next use behind this position?
def behind_use(uses: List<&2, Bind.Use>, +line: U32, +col: U32) -> Bool:
  match uses:
    case Nil{}:
      False{}
    case Con{Bind.Use{n, +l, c, tg}, rest}:
      Bool.or(U32.is_lt(l, line), Bool.and(U32.is_eq(l, line), U32.is_lt(c, col)))

# the type of the next binder
def head_bind_kind(binds: List<&2, Bind.Bind>) -> U32:
  match binds:
    case Nil{}:
      5
    case Con{Bind.Bind{n, l, c, k, note}, rest}:
      of_kind(k, n)

# the type of a use, from what it refers to
def of_target(tg: Bind.Target, all: List<&2, Bind.Bind>, name: String, braced: Bool) -> U32:
  match tg:
    case Bind.TLocal{tl, tc}:
      of_maybe_kind(Bind.kind_at(all, tl, tc), name)
    case Bind.TItem{i}:
      of_maybe_kind(Bind.kind_of_item(all, i), name)
    case other:
      by_shape(name, braced)

# the type of the next use
def head_use_class(uses: List<&2, Bind.Use>, all: List<&2, Bind.Bind>, braced: Bool) -> U32:
  match uses:
    case Nil{}:
      5
    case Con{Bind.Use{n, l, c, tg}, rest}:
      of_target(tg, all, n, braced)

# the binders after the next
def tail_binds(binds: List<&2, Bind.Bind>) -> List<&2, Bind.Bind>:
  match binds:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      t

# the uses after the next
def tail_uses(uses: List<&2, Bind.Use>) -> List<&2, Bind.Use>:
  match uses:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      t

# a token's class, when it has one, and the cursor after it
type Step is Data:
  Step{typ: Maybe<&2, U32>, cur: Cursor}

# the class of a name: the use that sits on its head, else its own shape
def use_class(+hu: Bool, +us: List<&2, Bind.Use>, +all: List<&2, Bind.Bind>, +name: String, +braced: Bool) -> U32:
  match hu:
    case True{}:
      head_use_class(us, all, braced)
    case False{}:
      by_shape(name, braced)

# a name token's type, taking the binder or the use that sits on it, and the
# cursor after it
def name_step(cur: Cursor, +all: List<&2, Bind.Bind>, +name: String, +line: U32, +col: U32, +braced: Bool) -> Step:
  Cursor{+binds, +uses} = cur
  +bs = Bool.pick(List<&2, Bind.Bind>, behind_bind(binds, line, col), tail_binds(binds), binds)
  +us = Bool.pick(List<&2, Bind.Use>, behind_use(uses, line, col), tail_uses(uses), uses)
  +hb = at_head_bind(bs, line, col)
  +hu = at_head_use(us, line, col)
  +of_use = use_class(hu, us, all, name, braced)
  +typ = Bool.pick(U32, hb, head_bind_kind(bs), of_use)
  Step{Some{typ}, Cursor{Bool.pick(List<&2, Bind.Bind>, hb, tail_binds(bs), bs),
    Bool.pick(List<&2, Bind.Use>, hu, tail_uses(us), us)}}

# names ask the binder; keywords are keywords; comments, strings and numbers
# are left to the editor's grammar, which tells a doc comment from a plain one
def of_tok(kk: Lex.TokKind, cur: Cursor, all: List<&2, Bind.Bind>, name: String, line: U32, col: U32, braced: Bool) ->
  Step:
  match kk:
    case Lex.TKey{}:
      Step{Some{0}, cur}
    case Lex.TName{}:
      name_step(cur, all, name, line, col, braced)
    case Lex.TUpper{}:
      name_step(cur, all, name, line, col, braced)
    case Lex.TDotted{}:
      name_step(cur, all, name, line, col, braced)
    case other:
      Step{None{}, cur}

# does the token list start with `{`?
def opens_brace(toks: List<&2, Lex.Tok>) -> Bool:
  match toks:
    case Con{Lex.Tok{k, +t, l, c}, rest}:
      String.eq(t, "{")
    case Nil{}:
      False{}

# a step's type
def typ_of(st: Step) -> Maybe<&2, U32>:
  Step{typ, cur} = st
  typ

# a step's cursor
def cur_of(st: Step) -> Cursor:
  Step{typ, cur} = st
  cur

# a classified token onto the list, when it has a type
def put(mm: Maybe<&2, U32>, +line: U32, +col: U32, +len: U32, rest: List<&2, Sem>) -> List<&2, Sem>:
  match mm:
    case None{}:
      rest
    case Some{typ}:
      Sem{line, col, len, typ} <> rest

# every token, in order, against the cursor
def classify(toks: List<&2, Lex.Tok>, cur: Cursor, +all: List<&2, Bind.Bind>) -> List<&2, Sem>:
  match toks:
    case Nil{}:
      Nil{}
    case Con{Lex.Tok{k, +t, +l, +c}, +rest}:
      +st = of_tok(k, cur, all, t, l, c, opens_brace(rest))
      put(typ_of(st), l, c, U32.from_nat(String.length(t)), classify(rest, cur_of(st), all))

# LSP's encoding: five numbers a token, positions relative to the previous
# token (a line delta, and a column delta on the same line, absolute on a new
# one)
def encode(sems: List<&2, Sem>, +pl: U32, +pc: U32) -> List<&2, U32>:
  match sems:
    case Nil{}:
      Nil{}
    case Con{Sem{+line, +col, len, typ}, rest}:
      +same = U32.is_eq(line, pl)
      +dcol = Bool.pick(U32, same, (col - pc : U32), col)
      (line - pl : U32) <> (dcol <> (len <> (typ <> (0 <> encode(rest, line, col)))))

def data.of(bb: Bind.Bound, toks: List<&2, Lex.Tok>) -> List<&2, U32>:
  Bind.Bound{+binds, uses, scopes} = bb
  encode(classify(toks, Cursor{binds, uses}, binds), 0, 0)

# a document's semantic tokens, encoded
def data(+text: String) -> List<&2, U32>:
  data.of(Bind.bound(text), Lex.tokens(text))
