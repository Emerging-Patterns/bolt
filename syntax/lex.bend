# syntax/lex: a source as tokens with positions. Lossless: every char lands
# in exactly one token, so the texts concatenate back to the source, whatever
# the source is -- an unclosed string ends at its line's end rather than
# swallowing the file. One char per step, a tail-recursive state machine.
#
# A name is letters, digits, `_` and `.` (`List.map`, `M.go`). Operator chars
# group into runs (`->`, `<-`, `=>`, `==`, `++`), except `:`, which always
# stands alone: `List<U32>:` must not read `>:`.
import Base

type TokKind is Data:
  TName{}
  TNum{}
  TStr{}
  TChar{}
  TComment{}
  TSpace{}
  TNewline{}
  TOp{}
  TOpen{}
  TClose{}
  TComma{}

# line and col are 0-based, of the token's first char
type Tok is Data:
  Tok{kind: TokKind, text: String, line: U32, col: U32}

type Class is Data:
  CAlpha{}
  CDigit{}
  CDot{}
  CQuote{}
  CTick{}
  CBack{}
  CHash{}
  CSpace{}
  CNewline{}
  COp{}
  CColon{}
  COpen{}
  CClose{}
  CComma{}

# what the machine is inside of; Fresh: the next char starts a token
type Mode is Data:
  Fresh{}
  InName{}
  InNum{}
  InStr{}
  InStrEsc{}
  InChar{}
  InCharEsc{}
  InComment{}
  InSpace{}
  InOp{}

# buf and toks are reversed; (sl, sc) is where the current token started
type St is Data:
  St{mode: Mode, kind: TokKind, line: U32, col: U32, sl: U32, sc: U32, buf: List<&2, Char>, toks: List<&2, Tok>}

def classify(+c: Char) -> Class:
  match c:
    case '.':
      CDot{}
    case '"':
      CQuote{}
    case '\'':
      CTick{}
    case '\\':
      CBack{}
    case '#':
      CHash{}
    case ' ':
      CSpace{}
    case '\t':
      CSpace{}
    case '\r':
      CSpace{}
    case '\n':
      CNewline{}
    case ':':
      CColon{}
    case ',':
      CComma{}
    case '(':
      COpen{}
    case '[':
      COpen{}
    case '{':
      COpen{}
    case ')':
      CClose{}
    case ']':
      CClose{}
    case '}':
      CClose{}
    case '_':
      CAlpha{}
    case other:
      Bool.pick(Class, Char.is_alpha(other), CAlpha{}, Bool.pick(Class, Char.is_digit(other), CDigit{}, COp{}))

# does a char of this class continue the token the machine is inside of?
def continues(m: Mode, cls: Class) -> Bool:
  match m cls:
    case Fresh{} c:
      False{}
    case InName{} CAlpha{}:
      True{}
    case InName{} CDigit{}:
      True{}
    case InName{} CDot{}:
      True{}
    case InNum{} CDigit{}:
      True{}
    case InNum{} CDot{}:
      True{}
    case InNum{} CAlpha{}:
      True{}
    case InStr{} CNewline{}:
      False{}
    case InStr{} c:
      True{}
    case InStrEsc{} CNewline{}:
      False{}
    case InStrEsc{} c:
      True{}
    case InChar{} CNewline{}:
      False{}
    case InChar{} c:
      True{}
    case InCharEsc{} CNewline{}:
      False{}
    case InCharEsc{} c:
      True{}
    case InComment{} CNewline{}:
      False{}
    case InComment{} c:
      True{}
    case InSpace{} CSpace{}:
      True{}
    case InOp{} COp{}:
      True{}
    case InOp{} CDot{}:
      True{}
    case m c:
      False{}

# the mode after a char that continued the token
def after(m: Mode, cls: Class) -> Mode:
  match m cls:
    case InStr{} CQuote{}:
      Fresh{}
    case InStr{} CBack{}:
      InStrEsc{}
    case InStrEsc{} c:
      InStr{}
    case InChar{} CTick{}:
      Fresh{}
    case InChar{} CBack{}:
      InCharEsc{}
    case InCharEsc{} c:
      InChar{}
    case m c:
      m

# the mode and the kind of the token a char starts
def begin.mode(cls: Class) -> Mode:
  match cls:
    case CAlpha{}:
      InName{}
    case CDigit{}:
      InNum{}
    case CQuote{}:
      InStr{}
    case CTick{}:
      InChar{}
    case CHash{}:
      InComment{}
    case CSpace{}:
      InSpace{}
    case COp{}:
      InOp{}
    case CDot{}:
      InOp{}
    case CBack{}:
      InOp{}
    case other:
      Fresh{}

def begin.kind(cls: Class) -> TokKind:
  match cls:
    case CAlpha{}:
      TName{}
    case CDigit{}:
      TNum{}
    case CQuote{}:
      TStr{}
    case CTick{}:
      TChar{}
    case CHash{}:
      TComment{}
    case CSpace{}:
      TSpace{}
    case CNewline{}:
      TNewline{}
    case COpen{}:
      TOpen{}
    case CClose{}:
      TClose{}
    case CComma{}:
      TComma{}
    case other:
      TOp{}

def word(buf: List<&2, Char>) -> String:
  String.from_list(List.reverse(&2, Char, buf))

# the token so far joins the others
def flush(kind: TokKind, sl: U32, sc: U32, +buf: List<&2, Char>, +toks: List<&2, Tok>) -> List<&2, Tok>:
  Bool.pick(List<&2, Tok>, List.is_empty(&2, Char, buf), toks, Tok{kind, word(buf), sl, sc} <> toks)

def is_newline(cls: Class) -> Bool:
  match cls:
    case CNewline{}:
      True{}
    case other:
      False{}

def step(+c: Char, st: St) -> St:
  St{+mode, +kind, +line, +col, +sl, +sc, +buf, +toks} = st
  +cls = classify(c)
  +nl = is_newline(cls)
  +line2 = Bool.pick(U32, nl, (line + 1 : U32), line)
  +col2 = Bool.pick(U32, nl, 0, (col + 1 : U32))
  Bool.pick(St, continues(mode, cls),
    St{after(mode, cls), kind, line2, col2, sl, sc, c <> buf, toks},
    St{begin.mode(cls), begin.kind(cls), line2, col2, line, col, [c], flush(kind, sl, sc, buf, toks)})

def run(cs: List<&2, Char>, st: St) -> St:
  match cs:
    case Nil{}:
      st
    case Con{c, t}:
      run(t, step(c, st))

def finish(st: St) -> List<&2, Tok>:
  St{mode, kind, line, col, sl, sc, buf, toks} = st
  List.reverse(&2, Tok, flush(kind, sl, sc, buf, toks))

def tokens(source: String) -> List<&2, Tok>:
  finish(run(String.to_list(source), St{Fresh{}, TSpace{}, 0, 0, 0, 0, [], []}))

# the tokens' texts, back to back: the source
def text.go(toks: List<&2, Tok>, acc: List<&2, String>) -> List<&2, String>:
  match toks:
    case Nil{}:
      acc
    case Con{Tok{k, t, l, c}, rest}:
      text.go(rest, t <> acc)

def text(toks: List<&2, Tok>) -> String:
  String.concat(List.reverse(&2, String, text.go(toks, [])))

# not space, a newline or a comment
def significant(k: TokKind) -> Bool:
  match k:
    case TSpace{}:
      False{}
    case TNewline{}:
      False{}
    case TComment{}:
      False{}
    case other:
      True{}
