# A finding whose line carries a `# noqa:` comment naming its code is not
# reported and not counted: a comment token whose text is `#`, any spaces,
# `noqa:` and then codes (runs of ASCII letters and digits, case-sensitive,
# split by commas with spaces around them allowed, any text after) silences
# every graded finding of its own file on its own line whose code it names,
# once every rule has run, the project rules included, and the summary and the
# exit status count only what remains. The filter reads comment tokens only,
# so a `noqa` inside a string literal is never one and no rule's findings
# change.
#
# also rests on: laws/ExitOnError.bend, laws/LastLineSummary.bend,
# laws/LinesInOrder.bend, laws/NoqaBare.bend, laws/NoqaBareText.bend
import Base
import ../src/finding.bend as F
import ../src/codes.bend as Codes
import ../src/rules/laws/law.bend as Law
import ../src/noqa.bend as Noqa
import ../src/syntax/lex.bend as Lex
import ./defs/NoqaSpacing.bend as D1

# Silencing (laws/NoqaSilencesNamedFindings.bend, laws/NoqaReportsStaleComments.bend). A noqa comment is read from the
# lexer's comment tokens alone, and silences a finding when it sits on the
# finding's line in the finding's file and names the finding's code. The
# `noqa` rule then reports each bare comment and each code that silenced
# nothing. The specs below are written apart from src/noqa.bend and
# rules/style/noqa.bend: strict Bool.and/Bool.or folds where those stop early.

# only comment tokens: every other token dropped. Law vocabulary.
def nq.comments(toks: List<&2, Lex.Tok>) -> List<&2, Lex.Tok>:
  match toks:
    case Nil{}:
      Nil{}
    case Con{Lex.Tok{Lex.TComment{}, t, l, c}, rest}:
      Lex.Tok{Lex.TComment{}, t, l, c} <> nq.comments(rest)
    case Con{_tk, rest}:
      nq.comments(rest)

# LAW: a file's noqa marks are read from its comment tokens alone: dropping
# every other token (strings, names, everything that is code) changes none,
# so a `noqa` inside a string literal is never one
law noqa_comments:
  for toks: List<&2, Lex.Tok>
  {Noqa.marks(toks) == Noqa.marks(nq.comments(toks)) : List<&2, Noqa.Mark>}

# LAW: a comment that is `#`, any number of spaces, `noqa:` and then any
# text is one mark, at the comment, naming the codes that text lists
law noqa_codes:
  for line: U32
  for col: U32
  for len: U32
  for n: Nat
  for tt: String
  {Noqa.mark.text(line, col, len, "#" ++ D1.nq.spaces(n) ++ "noqa:" ++ tt) == [Noqa.Mark{line, col, len,
      Noqa.codes(tt)}]
    : List<&2, Noqa.Mark>}

# the codes hold this one
def nq.has(cs: List<&2, String>, +code: String) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case Con{c, rest}:
      Bool.or(String.eq(c, code), nq.has(rest, code))

# some mark on the line names the code
def nq.on(mks: List<&2, Noqa.Mark>, +line: U32, +code: String) -> Bool:
  match mks:
    case Nil{}:
      False{}
    case Con{Noqa.Mark{l, _col, _len, cs}, rest}:
      Bool.or(Bool.and(U32.is_eq(l, line), nq.has(cs, code)), nq.on(rest, line, code))

# some mark of the file at the path, on the line, names the code
def nq.named(ms: List<&2, Noqa.Marks>, +path: String, +line: U32, +code: String) -> Bool:
  match ms:
    case Nil{}:
      False{}
    case Con{Noqa.Marks{p, mks}, rest}:
      Bool.or(Bool.and(String.eq(p, path), nq.on(mks, line, code)), nq.named(rest, path, line, code))

# a graded finding kept onto the rest, unless a mark names it
def nq.kept.one(+ms: List<&2, Noqa.Marks>, gg: F.Graded, +rest: List<&2, F.Graded>) -> List<&2, F.Graded>:
  F.Graded{ll, F.Finding{+path, +line, col, len, +rule, msg}} = gg
  Bool.pick(List<&2, F.Graded>, nq.named(ms, path, line, Codes.code(rule)), rest,
    F.Graded{ll, F.Finding{path, line, col, len, rule, msg}} <> rest)

# the graded findings no mark names, in order
def nq.kept(+ms: List<&2, Noqa.Marks>, gs: List<&2, F.Graded>) -> List<&2, F.Graded>:
  match gs:
    case Nil{}:
      Nil{}
    case Con{g, rest}:
      nq.kept.one(ms, g, nq.kept(ms, rest))

# LAW: the filter keeps exactly the graded findings that no mark of their own
# file, on their own line, names by their code, in order, and drops the rest
law noqa_keeps:
  for +ms: List<&2, Noqa.Marks>
  for gs: List<&2, F.Graded>
  {Noqa.keep(ms, gs) == nq.kept(ms, gs) : List<&2, F.Graded>}

# LAW: in a noqa comment's code list a space is a space, a comma a comma, a
# letter or a digit part of a code, and anything else ends the list
law code_list_chars:
  for +cc: Char
  {Noqa.cls(cc)
    == Bool.pick(Noqa.Cls, Char.is_eq(cc, ' '), Noqa.CSpace{},
      Bool.pick(Noqa.Cls, Char.is_eq(cc, ','), Noqa.CComma{},
        Bool.pick(Noqa.Cls, Bool.or(Char.is_alpha(cc), Char.is_digit(cc)), Noqa.CCode{}, Noqa.COther{})))
    : Noqa.Cls}
