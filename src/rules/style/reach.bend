# rule reach: a one-character name read far below where it is bound. A
# reader who meets `n` forty lines under its binder has only the letter to go
# on; within a few lines the binder is in sight and the letter is enough.
# Reported: a parameter, a let, do-bind or lambda name, or a pattern name,
# that some use reads from more than `max` lines below the line that binds
# it, by a name spelled with one character. One finding, on the binder.
# `max` is 20 unless the file's bolt.bend sets `def reach_max() -> U32`.
# A name is spelled with one character when, its `_` aside, it holds one
# letter or digit, however many times it is written: `n`, `nn`, `n_` and
# `ttt` are one character each, `xs`, `n2` and `c0` are two. A letter written
# twice says what the letter said, so it is read as the letter.
# Left alone: one capital letter (`A`, `T`: a type), a quantity parameter
# (bare, or typed `Quant`), a law's `for` names, an item, a field and a
# type-level binder, and every binder of a def that is a proof (no type,
# `def f(x):`, or one that returns `-> {..}`:
# src/rules/suspicious/empty.bend's reading of one), whose names are the
# law's. A PROOF.bend is exempt.
# The fix is a name that says what the value is, or a def short enough that
# the binder stays in sight. The 20: in public Bend 2 code a one-character
# name is read a median of 1 line below its binder, and 99 in 100 within 19
# (parameters; lets within 12, patterns within 9).
# A letter that is a convention (`x` and `y` of a position, the `a` to `h`
# of a hash round) reads no worse far away, and no token tells it from one
# that is a shrug: of 30 findings on public code read by hand, about 6 in
# 10 were names a word plainly helps. The rule is on with `style` all the
# same, as part of a house style; a `# noqa: S008` keeps a letter that is
# the word.
# This rule replaced `param` (S004), a two-character minimum on parameter
# names: under it `n` became `nn` one for one (30% of public parameters are
# one letter and 0.2% a doubled one; in trees linted by it, 1% and 22 to
# 33%), which is why a repeated letter counts once here.
import Base
import ../../paths.bend as Paths
import ../../role.bend as Role
import ../../src.bend as Src
import ../../finding.bend as F
import ../../syntax/bind.bend as Bind
import ../../syntax/lex.bend as Lex
import ../../lazy/lazy.bend as Lazy
import ../tokens.bend as T
import ../suspicious/empty.bend as Empty

# how many lines below its binder a one-character name may be read, unless
# a bolt.bend says otherwise
def limit() -> U32:
  20

# is the char `_`?
def one.under(ch: Char) -> Bool:
  Char.is_eq(ch, '_')

# is every char the one given, or `_`?
def one.all(cs: List<&2, Char>, +ch: Char) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{+c, t}:
      Lazy.and_then(Bool.or(one.under(c), Char.is_eq(c, ch)), _u => one.all(t, ch))

# the chars, their `_` aside, are one char written one or more times
def one.go(cs: List<&2, Char>) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case Con{+c, +t}:
      Lazy.either(Bool, one.under(c), _u => one.go(t), _v => one.all(t, c))

# is the name spelled with one character?
def one(name: String) -> Bool:
  one.go(String.to_list(name))

# the binder a use reads from more than max lines below it, by a
# one-character name: a use of anything but a binder of the file reads none
def far.hit(name: String, line: U32, t: Bind.Target, max: U32) -> Maybe<&2, Bind.Pos>:
  match t:
    case Bind.TLocal{+tl, tc}:
      Bool.pick(Maybe<&2, Bind.Pos>, Lazy.and_then(U32.is_gt(line, (tl + max : U32)), _u => one(name)),
        Some{Bind.Pos{tl, tc}}, None{})
    case other:
      None{}

# a binder read from afar, when there is one, onto the rest
def far.keep(m: Maybe<&2, Bind.Pos>, more: List<&2, Bind.Pos>) -> List<&2, Bind.Pos>:
  match m:
    case None{}:
      more
    case Some{p}:
      p <> more

# the binders the uses read from afar by a one-character name, one for each
# such use
def far(uses: List<&2, Bind.Use>, +max: U32) -> List<&2, Bind.Pos>:
  match uses:
    case Nil{}:
      Nil{}
    case Con{Bind.Use{name, line, _col, t}, rest}:
      far.keep(far.hit(name, line, t, max), far(rest, max))

# is the position this line and column?
def reaches.at(p: Bind.Pos, line: U32, col: U32) -> Bool:
  Bind.Pos{pl, pc} = p
  Bool.and(U32.is_eq(pl, line), U32.is_eq(pc, col))

# is the binder at this line and column among those read from afar?
def reaches(fr: List<&2, Bind.Pos>, +line: U32, +col: U32) -> Bool:
  match fr:
    case Nil{}:
      False{}
    case Con{p, rest}:
      Lazy.or_else(reaches.at(p, line, col), _u => reaches(rest, line, col))

# a parameter, a let, do-bind or lambda name, or a pattern name
def kind(k: Bind.BindKind) -> Bool:
  match k:
    case Bind.KParam{}:
      True{}
    case Bind.KLocal{}:
      True{}
    case Bind.KPat{}:
      True{}
    case other:
      False{}

# a parameter
def is_param(k: Bind.BindKind) -> Bool:
  match k:
    case Bind.KParam{}:
      True{}
    case other:
      False{}

# one character, and a capital: a type parameter
def letter(cs: List<&2, Char>) -> Bool:
  match cs:
    case Con{c, Nil{}}:
      Char.is_upper(c)
    case other:
      False{}

# `A`, `T`, `H`
def upper(nm: String) -> Bool:
  letter(String.to_list(nm))

# no type, or `: Quant`: a quantity parameter (`a` in `List<a, A>`). The
# note is read with its string literals cut to their quote: a `:` inside a
# string is no type
def quant(+note: String) -> Bool:
  +cn = T.code(note)
  Bool.or(Bool.not(String.contains(cn, ":")), String.ends_with(cn, ": Quant"))

# a type parameter, or a parameter that is a quantity: left alone. Only a
# parameter's note is its own declaration; a let's is its whole line
def allowed(k: Bind.BindKind, nm: String, note: String) -> Bool:
  Lazy.or_else(upper(nm), _u => Lazy.and_then(is_param(k), _v => quant(note)))

# is the line among these?
def has(ls: List<&2, U32>, +line: U32) -> Bool:
  match ls:
    case Nil{}:
      False{}
    case Con{l, rest}:
      Lazy.or_else(U32.is_eq(l, line), _u => has(rest, line))

# is the keyword `def`?
def proofs.is_def(k: Lex.TokKind, t: String) -> Bool:
  match k:
    case Lex.TKey{}:
      String.eq(t, "def")
    case other:
      False{}

# the line of the first token, where a def's name is
def proofs.line(toks: List<&2, Lex.Tok>) -> U32:
  match toks:
    case Nil{}:
      0
    case Con{Lex.Tok{_k, _t, l, _c}, _rest}:
      l

# the lines of the names of the defs that are proofs, among the significant
# tokens: the token after each `def` whose header Empty.proofy reads as one
def proofs(toks: List<&2, Lex.Tok>) -> List<&2, U32>:
  match toks:
    case Nil{}:
      Nil{}
    case Con{Lex.Tok{k, t, _l, _c}, +rest}:
      +more = proofs(rest)
      +hit = Lazy.and_then(proofs.is_def(k, t), _u => Empty.proofy(rest, 0n, False{}))
      Bool.pick(List<&2, U32>, hit, proofs.line(rest) <> more, more)

# the line of the item a binder sits in: its own when it is the item
def at_item(k: Bind.BindKind, line: U32, item: U32) -> U32:
  match k:
    case Bind.KItem{}:
      line
    case other:
      item

# is the binder reported? Read from afar, of a kind that counts, not left
# alone, and in no def that is a proof. The first test fails for nearly
# every binder, and nothing after it is read then
def flagged(
  +fr: List<&2, Bind.Pos>,
  +line: U32,
  +col: U32,
  +k: Bind.BindKind,
  nm: String,
  note: String,
  ps: List<&2, U32>,
  item: U32
) -> Bool:
  Lazy.and_then(reaches(fr, line, col),
    _u => Lazy.and_then(kind(k),
      _v => Lazy.and_then(Bool.not(allowed(k, nm, note)), _w => Bool.not(has(ps, item)))))

# what a finding says
def say(nm: String, max: U32) -> String:
  "Name " ++ nm ++ " is one character, read more than " ++ U32.show(max) ++ " lines below where it is bound;"
    ++ " name what it holds, or shorten the def."

# a finding on the binder when it is reported, before the rest
def found(
  hit: Bool,
  +nm: String,
  line: U32,
  col: U32,
  path: String,
  max: U32,
  more: List<&2, F.Finding>
) -> List<&2, F.Finding>:
  match hit:
    case True{}:
      F.Finding{path, line, col, U32.from_nat(String.length(nm)), "reach", say(nm, max)} <> more
    case False{}:
      more

# every reported binder, in order. item: the line of the item the binders
# so far sit in
def check.go(
  binds: List<&2, Bind.Bind>,
  +fr: List<&2, Bind.Pos>,
  +ps: List<&2, U32>,
  +path: String,
  +item: U32,
  +max: U32
) -> List<&2, F.Finding>:
  match binds:
    case Nil{}:
      Nil{}
    case Con{Bind.Bind{+nm, +line, +col, +kind, note}, rest}:
      +at = at_item(kind, line, item)
      found(flagged(fr, line, col, kind, nm, note, ps, at), nm, line, col, path, max,
        check.go(rest, fr, ps, path, at, max))

# the findings, given the binders read from afar: with none there is nothing
# to report, and the tokens are not read for the defs that are proofs
def check.far(
  fr: List<&2, Bind.Pos>,
  binds: List<&2, Bind.Bind>,
  toks: List<&2, Lex.Tok>,
  +path: String,
  max: U32
) -> List<&2, F.Finding>:
  match fr:
    case Nil{}:
      Nil{}
    case Con{p, rest}:
      check.go(binds, p <> rest, proofs(T.sig(toks)), path, 0, max)

# the rule over a file's binders, uses and tokens; a PROOF.bend's names are
# the law's
def check.on(
  binds: List<&2, Bind.Bind>,
  uses: List<&2, Bind.Use>,
  toks: List<&2, Lex.Tok>,
  +path: String,
  +max: U32
) -> List<&2, F.Finding>:
  Lazy.stop(List<&2, F.Finding>, Paths.is_proof(path), [],
    _u => check.far(far(uses, max), binds, toks, path, max))

# the rule, at a limit
def check(s: Src.Src, max: U32) -> List<&2, F.Finding>:
  Src.Src{path, _text, toks, _tree, bound, _items} = s
  Bind.Bound{binds, uses, _scopes} = bound
  check.on(binds, uses, toks, path, max)

# the rule at a limit, told the file's role (src/role.bend): a proof file is
# skipped
def check.role(r: Role.Role, s: Src.Src, +max: U32) -> List<&2, F.Finding>:
  Src.Src{path, _text, toks, _tree, bound, _items} = s
  Bind.Bound{binds, uses, _scopes} = bound
  Lazy.stop(List<&2, F.Finding>, Role.is_proof(r), [],
    _u => check.far(far(uses, max), binds, toks, path, max))
