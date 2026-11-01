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
        rr => List.append(&2, Noqa.Mark, Noqa.mark.text(l, c, U32.from_nat(String.length(t)), t), rr),
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

def Laws.noqa_codes(line, col, len, n, tt):
  Equal.cong(String, List<&2, Noqa.Mark>, ss => Noqa.mark.word(line, col, len, ss),
    Noqa.lead(D1.nq.spaces(n) ++ "noqa:" ++ tt), Noqa.lead("noqa:" ++ tt), M2.nqp.lead3(n, "noqa:", tt))

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

def Laws.noqa_keeps(ms, gs):
  match gs:
    case Nil{}:
      {==}
    case Con{F.Graded{+ll, F.Finding{+path, +line, +col, +len, +rule, +msg}}, +rest}:
      e = Equal.sym(Bool, Noqa.silenced(ms, path, line, Codes.code(rule)),
        Laws.nq.named(ms, path, line, Codes.code(rule)), nqp.silenced(ms, path, line, Codes.code(rule)))
      %e : {Bool.pick(List<&2, F.Graded>, _, Noqa.keep(ms, rest),
          F.Graded{ll, F.Finding{path, line, col, len, rule, msg}} <> Noqa.keep(ms, rest))
        == Laws.nq.kept(ms, F.Graded{ll, F.Finding{path, line, col, len, rule, msg}} <> rest) : List<&2, F.Graded>}
      h = Equal.sym(List<&2, F.Graded>, Noqa.keep(ms, rest), Laws.nq.kept(ms, rest), Laws.noqa_keeps(ms, rest))
      %h : {Bool.pick(List<&2, F.Graded>, Laws.nq.named(ms, path, line, Codes.code(rule)), _,
          F.Graded{ll, F.Finding{path, line, col, len, rule, msg}} <> _)
        == Laws.nq.kept(ms, F.Graded{ll, F.Finding{path, line, col, len, rule, msg}} <> rest) : List<&2, F.Graded>}
      {==}
