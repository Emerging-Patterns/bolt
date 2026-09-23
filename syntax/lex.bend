# syntax/lex: a source as tokens with positions. Lossless: every char lands
# in exactly one token, so the texts concatenate back to the source, whatever
# the source is. A string runs to its closing quote across newlines, as in
# bend, so an unclosed one runs to the end of the file (bend rejects that
# file). A char literal and a comment end at their line's end. One char per
# step, a tail-recursive state machine.
#
# A name is letters, digits, `_` and `.` (`List.map`, `M.go`). Operator chars
# group into runs (`->`, `<-`, `=>`, `==`, `++`), except `:`, which always
# stands alone: `List<U32>:` must not read `>:`.
#
# Kinds tell apart what binds from what does not, so a walk over the tokens
# can branch by constructor: a keyword (TKey), a dotted name (TDotted: never
# a binder), a capitalized one (TUpper: a constructor before `{`, a type, or
# a binder), `_` (TWild), and the operators that bind: `:` `=` `<-` `->` `=>`
# `@` `&`.
import Base

# the kinds; TName is a plain name (lowercase, undotted): what a pattern can
# bind
type TokKind is Data:
  TName{}
  TUpper{}
  TDotted{}
  TWild{}
  TKey{}
  TNum{}
  TStr{}
  TChar{}
  TComment{}
  TSpace{}
  TNewline{}
  TOp{}
  TColon{}
  TEq{}
  TBind{}
  TArrow{}
  TLam{}
  TAll{}
  TAmp{}
  TOpen{}
  TClose{}
  TComma{}

# line and col are 0-based, of the token's first char
type Tok is Data:
  Tok{kind: TokKind, text: String, line: U32, col: U32}

# what a char is, for the machine
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

# the class of a code point, given the class any other character would get.
# Written as comparisons rather than as `case '.':` arms: a character literal
# in a pattern is a U32 literal inside a constructor pattern, and bend's C
# backend pays about 90 MB for each one -- these eighteen cost 1.57 GB as
# literal arms and 0.10 GB written this way.
def classify.go(+xx: U32, other: Class) -> Class:
  Bool.pick(Class, U32.is_eq(xx, 46), CDot{},  # '.'
  Bool.pick(Class, U32.is_eq(xx, 34), CQuote{},  # '"'
  Bool.pick(Class, U32.is_eq(xx, 39), CTick{},  # '\''
  Bool.pick(Class, U32.is_eq(xx, 92), CBack{},  # '\\'
  Bool.pick(Class, U32.is_eq(xx, 35), CHash{},  # '#'
  Bool.pick(Class, U32.is_eq(xx, 32), CSpace{},  # ' '
  Bool.pick(Class, U32.is_eq(xx, 9), CSpace{},  # '\t'
  Bool.pick(Class, U32.is_eq(xx, 13), CSpace{},  # '\r'
  Bool.pick(Class, U32.is_eq(xx, 10), CNewline{},  # '\n'
  Bool.pick(Class, U32.is_eq(xx, 58), CColon{},  # ':'
  Bool.pick(Class, U32.is_eq(xx, 44), CComma{},  # ','
  Bool.pick(Class, U32.is_eq(xx, 40), COpen{},  # '('
  Bool.pick(Class, U32.is_eq(xx, 91), COpen{},  # '['
  Bool.pick(Class, U32.is_eq(xx, 123), COpen{},  # '{'
  Bool.pick(Class, U32.is_eq(xx, 41), CClose{},  # ')'
  Bool.pick(Class, U32.is_eq(xx, 93), CClose{},  # ']'
  Bool.pick(Class, U32.is_eq(xx, 125), CClose{},  # '}'
  Bool.pick(Class, U32.is_eq(xx, 95), CAlpha{},  # '_'
    other))))))))))))))))))

# a char's class
def classify(+cc: Char) -> Class:
  +other = Bool.pick(Class, Char.is_alpha(cc), CAlpha{},
    Bool.pick(Class, Char.is_digit(cc), CDigit{}, COp{}))
  classify.go(Char.to_u32(cc), other)

# does a char of this class continue the token the machine is inside of?
def continues(mm: Mode, cls: Class) -> Bool:
  match mm cls:
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
    case InStr{} c:
      True{}
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
def after(mm: Mode, cls: Class) -> Mode:
  match mm cls:
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

# the buffered chars as a string, in order
def word(buf: List<&2, Char>) -> String:
  String.from_list(List.reverse(&2, Char, buf))

# is the text one of Bend's keywords?
def is_keyword(+tt: String) -> Bool:
  List.contains(~String, ~String.eq,
    ["def", "type", "law", "match", "case", "do", "return", "for", "exs", "where", "is", "import",
     "Type", "Data", "Kind", "Quant"], tt)

# does the text start with a capital?
def upper_first(cs: List<&2, Char>) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case Con{c, t}:
      Char.is_upper(c)

# a whole name's kind
def refine_name(+tt: String) -> TokKind:
  Bool.pick(TokKind, is_keyword(tt), TKey{},
    Bool.pick(TokKind, String.contains(tt, "."), TDotted{},
      Bool.pick(TokKind, String.eq(tt, "_"), TWild{},
        Bool.pick(TokKind, upper_first(String.to_list(tt)), TUpper{}, TName{}))))

# a whole operator's kind
def refine_op(+tt: String) -> TokKind:
  Bool.pick(TokKind, String.eq(tt, ":"), TColon{},
    Bool.pick(TokKind, String.eq(tt, "="), TEq{},
      Bool.pick(TokKind, String.eq(tt, "<-"), TBind{},
        Bool.pick(TokKind, String.eq(tt, "->"), TArrow{},
          Bool.pick(TokKind, String.eq(tt, "=>"), TLam{},
            Bool.pick(TokKind, Bool.or(String.eq(tt, "@"), Bool.or(String.eq(tt, "@+"), String.eq(tt, "@-"))), TAll{},
              Bool.pick(TokKind, String.eq(tt, "&"), TAmp{}, TOp{})))))))

# a name's or an operator's kind, once its text is whole
def refine(kind: TokKind, tt: String) -> TokKind:
  match kind:
    case TName{}:
      refine_name(tt)
    case TOp{}:
      refine_op(tt)
    case other:
      other

# the token so far joins the others
def flush(kind: TokKind, sl: U32, sc: U32, +buf: List<&2, Char>, +toks: List<&2, Tok>) -> List<&2, Tok>:
  +t = word(buf)
  Bool.pick(List<&2, Tok>, List.is_empty(&2, Char, buf), toks, Tok{refine(kind, t), t, sl, sc} <> toks)

# is the char a line break, '\n'? The one char whose class is CNewline
def is_newline(cc: Char) -> Bool:
  U32.is_eq(Char.to_u32(cc), 10)

# one char: it continues the current token, or starts a new one
def step(+cc: Char, st: St) -> St:
  St{+mode, +kind, +line, +col, +sl, +sc, +buf, +toks} = st
  +cls = classify(cc)
  +nl = is_newline(cc)
  +line2 = Bool.pick(U32, nl, (line + 1 : U32), line)
  +col2 = Bool.pick(U32, nl, 0, (col + 1 : U32))
  Bool.pick(St, continues(mode, cls),
    St{after(mode, cls), kind, line2, col2, sl, sc, cc <> buf, toks},
    St{begin.mode(cls), begin.kind(cls), line2, col2, line, col, [cc], flush(kind, sl, sc, buf, toks)})

# every char, in order
def run(cs: List<&2, Char>, st: St) -> St:
  match cs:
    case Nil{}:
      st
    case Con{c, t}:
      run(t, step(c, st))

# the tokens once the chars are over, the last one flushed
def finish(st: St) -> List<&2, Tok>:
  St{mode, kind, line, col, sl, sc, buf, toks} = st
  List.reverse(&2, Tok, flush(kind, sl, sc, buf, toks))

# a source as tokens
def tokens(source: String) -> List<&2, Tok>:
  finish(run(String.to_list(source), St{Fresh{}, TSpace{}, 0, 0, 0, 0, [], []}))

# the tokens' texts, back to back: the source
def text.go(toks: List<&2, Tok>, acc: List<&2, String>) -> List<&2, String>:
  match toks:
    case Nil{}:
      acc
    case Con{Tok{k, t, l, c}, rest}:
      text.go(rest, t <> acc)

# the tokens' texts, back to back: the source
def text(toks: List<&2, Tok>) -> String:
  String.concat(List.reverse(&2, String, text.go(toks, [])))

# an opening bracket?
def is_open(kk: TokKind) -> Bool:
  match kk:
    case TOpen{}:
      True{}
    case other:
      False{}

# a closing bracket?
def is_close(kk: TokKind) -> Bool:
  match kk:
    case TClose{}:
      True{}
    case other:
      False{}

# a comma?
def is_comma(kk: TokKind) -> Bool:
  match kk:
    case TComma{}:
      True{}
    case other:
      False{}

# any identifier: a name, a keyword, a dotted or a capitalized one, `_`
def is_name(kk: TokKind) -> Bool:
  match kk:
    case TName{}:
      True{}
    case TUpper{}:
      True{}
    case TDotted{}:
      True{}
    case TWild{}:
      True{}
    case TKey{}:
      True{}
    case other:
      False{}

# an operator of any kind
def is_op(kk: TokKind) -> Bool:
  match kk:
    case TOp{}:
      True{}
    case TColon{}:
      True{}
    case TEq{}:
      True{}
    case TBind{}:
      True{}
    case TArrow{}:
      True{}
    case TLam{}:
      True{}
    case TAll{}:
      True{}
    case TAmp{}:
      True{}
    case other:
      False{}

# a newline?
def is_nl(kk: TokKind) -> Bool:
  match kk:
    case TNewline{}:
      True{}
    case other:
      False{}

# not space, a newline or a comment
def significant(kk: TokKind) -> Bool:
  match kk:
    case TSpace{}:
      False{}
    case TNewline{}:
      False{}
    case TComment{}:
      False{}
    case other:
      True{}
