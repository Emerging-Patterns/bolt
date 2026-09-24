# bolt/noqa: `# noqa: CODE` comments, and the filter they make, after ruff.
# A comment token (the lexer's, so never a string's contents) whose text is
# `#`, any spaces, then `noqa` is a mark. A `:` right after `noqa` opens
# its codes: runs of ASCII letters and digits, split by commas with spaces
# around them allowed, the list ending at anything else, so free text may
# follow (`# noqa: L001 IO entry point`). `noqa` at the comment's end, or
# followed by a space, names no code: a bare mark. Codes are case-sensitive
# and are bolt/codes.bend's (`L001`, `U002`). A finding is silenced when a
# mark of its own file, on its own line, names its code.
#
# No rule reads this: the planner (lint/plan.bend) and the language server
# run `keep` over the graded findings once every rule has run, the project
# rules included, and then `noqa` (rules/style/noqa.bend) over what the
# marks silenced. Pure (GPU-safe).
import Base
import ../lazy/lazy.bend as Lazy
import ../syntax/lex.bend as Lex
import ./finding.bend as F
import ./codes.bend as Codes
import ./src.bend as Src

# one noqa comment: its line and column (0-based) and width, and the codes
# it names, none for a bare one
type Mark is Data:
  Mark{line: U32, col: U32, len: U32, codes: List<&2, String>}

# a file's noqa comments
type Marks is Data:
  Marks{path: String, marks: List<&2, Mark>}

# ---------------------------------------------------------------------------
# reading a comment

# what a char is to the code list: a space, a comma, a letter or digit, or
# anything else
type Cls is Data:
  CSpace{}
  CComma{}
  CCode{}
  COther{}

# a char's class
def cls(+cc: Char) -> Cls:
  +code = Bool.or(Char.is_alpha(cc), Char.is_digit(cc))
  +tail = Bool.pick(Cls, code, CCode{}, COther{})
  Bool.pick(Cls, Char.is_eq(cc, ' '), CSpace{}, Bool.pick(Cls, Char.is_eq(cc, ','), CComma{}, tail))

# where the code list reader stands: before a code (spaces allowed), inside
# one, after one (spaces, then a comma or the list's end), or past the list
type Phase is Data:
  Before{}
  Inside{}
  After{}
  Past{}

# the reader: where it stands, the code it is reading (its chars, the last
# first), and the codes read (the last first)
type Rd is Data:
  Rd{phase: Phase, buf: List<&2, Char>, acc: List<&2, String>}

# the chars read, the last first, as a code
def word(buf: List<&2, Char>) -> String:
  String.from_list(List.reverse(&2, Char, buf))

# before a code: a space waits, a letter or digit starts one, anything else
# ends the list
def step.before(kk: Cls, +cc: Char, +acc: List<&2, String>) -> Rd:
  match kk:
    case CSpace{}:
      Rd{Before{}, [], acc}
    case CComma{}:
      Rd{Past{}, [], acc}
    case CCode{}:
      Rd{Inside{}, [cc], acc}
    case COther{}:
      Rd{Past{}, [], acc}

# inside a code: a letter or digit extends it; a space, a comma or anything
# else ends it, and a comma expects the next
def step.inside(kk: Cls, +cc: Char, +buf: List<&2, Char>, +acc: List<&2, String>) -> Rd:
  match kk:
    case CSpace{}:
      Rd{After{}, [], word(buf) <> acc}
    case CComma{}:
      Rd{Before{}, [], word(buf) <> acc}
    case CCode{}:
      Rd{Inside{}, cc <> buf, acc}
    case COther{}:
      Rd{Past{}, [], word(buf) <> acc}

# after a code: a space waits, a comma expects the next, anything else ends
# the list
def step.after(kk: Cls, +acc: List<&2, String>) -> Rd:
  match kk:
    case CSpace{}:
      Rd{After{}, [], acc}
    case CComma{}:
      Rd{Before{}, [], acc}
    case CCode{}:
      Rd{Past{}, [], acc}
    case COther{}:
      Rd{Past{}, [], acc}

# the reader after one more char
def step.at(ph: Phase, +cc: Char, +buf: List<&2, Char>, +acc: List<&2, String>) -> Rd:
  match ph:
    case Before{}:
      step.before(cls(cc), cc, acc)
    case Inside{}:
      step.inside(cls(cc), cc, buf, acc)
    case After{}:
      step.after(cls(cc), acc)
    case Past{}:
      Rd{Past{}, buf, acc}

# the reader after one more char
def step(+cc: Char, rd: Rd) -> Rd:
  Rd{ph, buf, acc} = rd
  step.at(ph, cc, buf, acc)

# the reader after the text
def run(tt: String, rd: Rd) -> Rd:
  match tt:
    case SNil{}:
      rd
    case SCon{cc, rest}:
      run(rest, step(cc, rd))

# the codes read, in order, the one still being read included
def finish.at(ph: Phase, +buf: List<&2, Char>, +acc: List<&2, String>) -> List<&2, String>:
  match ph:
    case Before{}:
      List.reverse(&2, String, acc)
    case Inside{}:
      List.reverse(&2, String, word(buf) <> acc)
    case After{}:
      List.reverse(&2, String, acc)
    case Past{}:
      List.reverse(&2, String, acc)

# the codes read, in order
def finish(rd: Rd) -> List<&2, String>:
  Rd{ph, buf, acc} = rd
  finish.at(ph, buf, acc)

# the codes a text after `noqa:` names
def codes(tt: String) -> List<&2, String>:
  finish(run(tt, Rd{Before{}, [], []}))

# the text after its leading spaces
def lead(tt: String) -> String:
  match tt:
    case SCon{' ', rest}:
      lead(rest)
    case other:
      other

# a comment's text past `noqa`: a mark naming the codes after a `:`, a bare
# one at the end or before a space, and none for anything else (`noqas`)
def mark.rest(+line: U32, +col: U32, +len: U32, tt: String) -> List<&2, Mark>:
  match tt:
    case SNil{}:
      [Mark{line, col, len, []}]
    case SCon{':', rest}:
      [Mark{line, col, len, codes(rest)}]
    case SCon{' ', _rest}:
      [Mark{line, col, len, []}]
    case other:
      []

# a comment's text past `#` and its spaces: a mark when it opens with `noqa`
def mark.word(+line: U32, +col: U32, +len: U32, tt: String) -> List<&2, Mark>:
  match tt:
    case SCon{'n', SCon{'o', SCon{'q', SCon{'a', rest}}}}:
      mark.rest(line, col, len, rest)
    case other:
      []

# a comment's text: a mark when it is `#`, any spaces, then `noqa`
def mark.text(+line: U32, +col: U32, +len: U32, tt: String) -> List<&2, Mark>:
  match tt:
    case SCon{'#', rest}:
      mark.word(line, col, len, lead(rest))
    case other:
      []

# a comment token's mark, when it is one; any other token has none
def mark.of(tk: Lex.Tok) -> List<&2, Mark>:
  match tk:
    case Lex.Tok{Lex.TComment{}, +t, l, c}:
      mark.text(l, c, U32.from_nat(String.length(t)), t)
    case other:
      []

# the marks among the tokens, in order
def marks(toks: List<&2, Lex.Tok>) -> List<&2, Mark>:
  match toks:
    case Nil{}:
      Nil{}
    case Con{t, rest}:
      List.append(&2, Mark, mark.of(t), marks(rest))

# a file's marks, from its tokens
def file(path: String, toks: List<&2, Lex.Tok>) -> Marks:
  Marks{path, marks(toks)}

# each source's marks, in order
def of_srcs(ss: List<&2, Src.Src>) -> List<&2, Marks>:
  match ss:
    case Nil{}:
      Nil{}
    case Con{Src.Src{path, _text, toks, _tree, _bound, _items}, rest}:
      file(path, toks) <> of_srcs(rest)

# ---------------------------------------------------------------------------
# the filter

# the codes include this one
def named(cs: List<&2, String>, +code: String) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case Con{c, rest}:
      Lazy.or_else(String.eq(c, code), _u => named(rest, code))

# a mark on the line names the code
def on_line(mks: List<&2, Mark>, +line: U32, +code: String) -> Bool:
  match mks:
    case Nil{}:
      False{}
    case Con{Mark{l, _col, _len, cs}, rest}:
      Lazy.or_else(Lazy.and_then(U32.is_eq(l, line), _u => named(cs, code)), _v => on_line(rest, line, code))

# a mark of the file at the path, on the line, names the code
def silenced(ms: List<&2, Marks>, +path: String, +line: U32, +code: String) -> Bool:
  match ms:
    case Nil{}:
      False{}
    case Con{Marks{p, mks}, rest}:
      Lazy.or_else(Lazy.and_then(String.eq(p, path), _u => on_line(mks, line, code)),
        _v => silenced(rest, path, line, code))

# the graded findings no mark silences, in order
def keep(+ms: List<&2, Marks>, gs: List<&2, F.Graded>) -> List<&2, F.Graded>:
  match gs:
    case Nil{}:
      Nil{}
    case Con{F.Graded{ll, F.Finding{+path, +line, col, len, +rule, msg}}, rest}:
      +more = keep(ms, rest)
      Bool.pick(List<&2, F.Graded>, silenced(ms, path, line, Codes.code(rule)), more,
        F.Graded{ll, F.Finding{path, line, col, len, rule, msg}} <> more)
