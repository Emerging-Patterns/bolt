# proofs of laws/NoqaSilencesNamedFindings.bend
import Base
import ../src/lazy/lazy.bend as Lazy
import ../src/finding.bend as F
import ../src/noqa.bend as Noqa
import ../src/codes.bend as Codes
import ../src/syntax/lex.bend as Lex
import ../laws/NoqaSilencesNamedFindings.bend as Laws
import ../laws/defs/NoqaSpacing.bend as D1
import ./lemmas/NoqaEarlyExits.bend as M1
import ./lemmas/NoqaLeadingSpaces.bend as M2
import ./lemmas/BinderIndexIsContains.bend as M3
import ../src/syntax/bind.bend as Bind
import ../laws/BinderIndexFindsItems.bend as L1
import ./lemmas/BinderIndex.bend as M4

# silencing and the `noqa` rule (laws/NoqaSilencesNamedFindings.bend, laws/NoqaReportsStaleComments.bend)
# ----------------------------------

# one token onto the marks: a comment's mark is read alike on both sides,
# and any other token has none
law nqp.comments.at:
  for k: Lex.TokKind
  for +t: String
  for +l: U32
  for +c: U32
  for +rest: List<&2, Lex.Tok>
  for ih: {Noqa.marks(rest) == Noqa.marks(Laws.nq.comments(rest)) : List<&2, Noqa.Mark>}
  {Noqa.marks(Lex.Tok{k, t, l, c} <> rest) == Noqa.marks(Laws.nq.comments(Lex.Tok{k, t, l, c} <> rest))
    : List<&2, Noqa.Mark>}

def nqp.comments.at(k, t, l, c, rest, ih):
  match k:
    case Lex.TComment{}:
      Equal.cong(List<&2, Noqa.Mark>, List<&2, Noqa.Mark>,
        r => List.append(&2, Noqa.Mark, Noqa.mark.text(l, c, U32.from_nat(String.length(t)), t), r),
        Noqa.marks(rest), Noqa.marks(Laws.nq.comments(rest)), ih)
    case Lex.TName{}:
      ih
    case Lex.TUpper{}:
      ih
    case Lex.TDotted{}:
      ih
    case Lex.TWild{}:
      ih
    case Lex.TKey{}:
      ih
    case Lex.TNum{}:
      ih
    case Lex.TStr{}:
      ih
    case Lex.TChar{}:
      ih
    case Lex.TSpace{}:
      ih
    case Lex.TNewline{}:
      ih
    case Lex.TOp{}:
      ih
    case Lex.TColon{}:
      ih
    case Lex.TEq{}:
      ih
    case Lex.TBind{}:
      ih
    case Lex.TArrow{}:
      ih
    case Lex.TLam{}:
      ih
    case Lex.TAll{}:
      ih
    case Lex.TAmp{}:
      ih
    case Lex.TOpen{}:
      ih
    case Lex.TClose{}:
      ih
    case Lex.TComma{}:
      ih

def Laws.noqa_comments(toks):
  match toks:
    case Nil{}:
      {==}
    case Con{Lex.Tok{k, +t, +l, +c}, +rest}:
      nqp.comments.at(k, t, l, c, rest, Laws.noqa_comments(rest))

def Laws.noqa_codes(line, col, len, n, t):
  Equal.cong(String, List<&2, Noqa.Mark>, s => Noqa.mark.word(line, col, len, s),
    Noqa.lead(D1.nq.spaces(n) ++ "noqa:" ++ t), Noqa.lead("noqa:" ++ t), M2.nqp.lead3(n, "noqa:", t))

# the filter's search of a mark's codes is the spec's
law nqp.named:
  for cs: List<&2, String>
  for +code: String
  {Noqa.named(cs, code) == Laws.nq.has(cs, code) : Bool}

def nqp.named(cs, code):
  match cs:
    case Nil{}:
      {==}
    case Con{+c, +rest}:
      M1.nqp.or_else(String.eq(c, code), Noqa.named(rest, code), Laws.nq.has(rest, code), nqp.named(rest, code))

# the filter's search of a file's marks is the spec's
law nqp.on_line:
  for mks: List<&2, Noqa.Mark>
  for +line: U32
  for +code: String
  {Noqa.on_line(mks, line, code) == Laws.nq.on(mks, line, code) : Bool}

def nqp.on_line(mks, line, code):
  match mks:
    case Nil{}:
      {==}
    case Con{Noqa.Mark{+l, _col, _len, +cs}, +rest}:
      M1.nqp.or2(Lazy.and_then(U32.is_eq(l, line), _u => Noqa.named(cs, code)),
        Bool.and(U32.is_eq(l, line), Laws.nq.has(cs, code)),
        Noqa.on_line(rest, line, code), Laws.nq.on(rest, line, code),
        M1.nqp.and_then(U32.is_eq(l, line), Noqa.named(cs, code), Laws.nq.has(cs, code), nqp.named(cs, code)),
        nqp.on_line(rest, line, code))

# the filter's search of every file's marks is the spec's
law nqp.silenced:
  for ms: List<&2, Noqa.Marks>
  for +path: String
  for +line: U32
  for +code: String
  {Noqa.silenced(ms, path, line, code) == Laws.nq.named(ms, path, line, code) : Bool}

def nqp.silenced(ms, path, line, code):
  match ms:
    case Nil{}:
      {==}
    case Con{Noqa.Marks{+p, +mks}, +rest}:
      M1.nqp.or2(Lazy.and_then(String.eq(p, path), _u => Noqa.on_line(mks, line, code)),
        Bool.and(String.eq(p, path), Laws.nq.on(mks, line, code)),
        Noqa.silenced(rest, path, line, code), Laws.nq.named(rest, path, line, code),
        M1.nqp.and_then(String.eq(p, path), Noqa.on_line(mks, line, code), Laws.nq.on(mks, line, code),
          nqp.on_line(mks, line, code)),
        nqp.silenced(rest, path, line, code))

# an early and that the plain and absorbs is what it guards
law nqp.guard:
  for c: Bool
  for -s: Bool
  for ih: {Bool.and(c, s) == s : Bool}
  {Lazy.and_then(c, _u => s) == s : Bool}

def nqp.guard(c, _s, ih):
  match c:
    case True{}:
      {==}
    case False{}:
      ih

# a file that holds no mark: the search goes on to the rest, whatever its path
law nqp.none:
  for e: Bool
  for -c: Bool
  for -s: Bool
  for ih: {Bool.and(c, s) == s : Bool}
  {Bool.and(c, Lazy.or_else(Lazy.and_then(e, _u => False{}), _v => s))
    == Lazy.or_else(Lazy.and_then(e, _u => False{}), _v => s) : Bool}

def nqp.none(e, _c, _s, ih):
  match e:
    case True{}:
      ih
    case False{}:
      ih

# a file that holds a mark: its path is among the marked ones, so the search
# of its marks is kept, and past another file's the rest decides
law nqp.some:
  for e: Bool
  for -c: Bool
  for -o: Bool
  for -s: Bool
  for ih: {Bool.and(c, s) == s : Bool}
  {Bool.and(Lazy.or_else(e, _u => c), Lazy.or_else(Lazy.and_then(e, _u => o), _v => s))
    == Lazy.or_else(Lazy.and_then(e, _u => o), _v => s) : Bool}

def nqp.some(e, _c, _o, _s, ih):
  match e:
    case True{}:
      {==}
    case False{}:
      ih

# a mark silences a finding only in a file that holds a mark: the search
# finds nothing for a path that is not among the marked ones
law nqp.absorb:
  for ms: List<&2, Noqa.Marks>
  for +path: String
  for +line: U32
  for +code: String
  {Bool.and(Bind.has_item(Noqa.marked(ms), path), Noqa.silenced(ms, path, line, code))
    == Noqa.silenced(ms, path, line, code) : Bool}

def nqp.absorb(ms, path, line, code):
  match ms:
    case Nil{}:
      {==}
    case Con{Noqa.Marks{+p, Nil{}}, +rest}:
      nqp.none(String.eq(p, path), Bind.has_item(Noqa.marked(rest), path), Noqa.silenced(rest, path, line, code),
        nqp.absorb(rest, path, line, code))
    case Con{Noqa.Marks{+p, Con{+m, +mt}}, +rest}:
      %Equal.sym(Bool, Bind.same(p, path), String.eq(p, path), M3.ic.alike(p, path)) :
        {Bool.and(Lazy.or_else(_, _u => Bind.has_item(Noqa.marked(rest), path)),
          Noqa.silenced(Noqa.Marks{p, m <> mt} <> rest, path, line, code))
          == Noqa.silenced(Noqa.Marks{p, m <> mt} <> rest, path, line, code) : Bool}
      nqp.some(String.eq(p, path), Bind.has_item(Noqa.marked(rest), path), Noqa.on_line(m <> mt, line, code),
        Noqa.silenced(rest, path, line, code), nqp.absorb(rest, path, line, code))

# asking the index of the marked files first changes nothing the search finds
law nqp.filter:
  for +ms: List<&2, Noqa.Marks>
  for +path: String
  for +line: U32
  for +code: String
  {Lazy.and_then(Bind.indexed(Bind.index(Noqa.marked(ms)), path), _u => Noqa.silenced(ms, path, line, code))
    == Noqa.silenced(ms, path, line, code) : Bool}

def nqp.filter(ms, path, line, code):
  %Equal.sym(Bool, Bind.indexed(Bind.index(Noqa.marked(ms)), path), Bind.has_item(Noqa.marked(ms), path),
    L1.index_finds(Noqa.marked(ms), path)) :
    {Lazy.and_then(_, _u => Noqa.silenced(ms, path, line, code)) == Noqa.silenced(ms, path, line, code) : Bool}
  nqp.guard(Bind.has_item(Noqa.marked(ms), path), Noqa.silenced(ms, path, line, code),
    nqp.absorb(ms, path, line, code))

# the filter over the index of the marked files keeps what the spec keeps
law nqp.keeps:
  for +ms: List<&2, Noqa.Marks>
  for gs: List<&2, F.Graded>
  {Noqa.keep.fast(ms, Bind.index(Noqa.marked(ms)), gs) == Laws.nq.kept(ms, gs) : List<&2, F.Graded>}

def nqp.keeps(ms, gs):
  match gs:
    case Nil{}:
      {==}
    case Con{F.Graded{+l, F.Finding{+path, +line, +col, +len, +rule, +msg}}, +rest}:
      +ix = Bind.index(Noqa.marked(ms))
      +code = Codes.code(rule)
      %Equal.sym(Bool, Lazy.and_then(Bind.indexed(ix, path), _u => Noqa.silenced(ms, path, line, code)),
        Noqa.silenced(ms, path, line, code), nqp.filter(ms, path, line, code)) :
        {Bool.pick(List<&2, F.Graded>, _, Noqa.keep.fast(ms, ix, rest),
          F.Graded{l, F.Finding{path, line, col, len, rule, msg}} <> Noqa.keep.fast(ms, ix, rest))
          == Laws.nq.kept(ms, F.Graded{l, F.Finding{path, line, col, len, rule, msg}} <> rest) : List<&2, F.Graded>}
      e = Equal.sym(Bool, Noqa.silenced(ms, path, line, code),
        Laws.nq.named(ms, path, line, code), nqp.silenced(ms, path, line, code))
      %e : {Bool.pick(List<&2, F.Graded>, _, Noqa.keep.fast(ms, ix, rest),
          F.Graded{l, F.Finding{path, line, col, len, rule, msg}} <> Noqa.keep.fast(ms, ix, rest))
        == Laws.nq.kept(ms, F.Graded{l, F.Finding{path, line, col, len, rule, msg}} <> rest) : List<&2, F.Graded>}
      h = Equal.sym(List<&2, F.Graded>, Noqa.keep.fast(ms, ix, rest), Laws.nq.kept(ms, rest), nqp.keeps(ms, rest))
      %h : {Bool.pick(List<&2, F.Graded>, Laws.nq.named(ms, path, line, code), _,
          F.Graded{l, F.Finding{path, line, col, len, rule, msg}} <> _)
        == Laws.nq.kept(ms, F.Graded{l, F.Finding{path, line, col, len, rule, msg}} <> rest) : List<&2, F.Graded>}
      {==}

def Laws.noqa_keeps(ms, gs):
  nqp.keeps(ms, gs)

def Laws.code_list_chars(_cc):
  {==}
