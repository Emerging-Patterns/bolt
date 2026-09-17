# json/lex: text to tokens, one char per step: a tail-recursive state machine
# over the char list, so it needs no fuel and runs as a loop.
import Base

type Tok is Data:
  TOpenArr{}
  TCloseArr{}
  TOpenObj{}
  TCloseObj{}
  TColon{}
  TComma{}
  TStr{s: String}
  TWord{raw: String}
  TBad{}

type Class is Data:
  CPunct{t: Tok}
  CQuote{}
  CBack{}
  CSpace{}
  COther{}

type Mode is Data:
  Idle{}
  Word{}
  Str{}
  Esc{}
  Uni{left: Nat, acc: U32}

# the lexer's state: buf and toks are both reversed
type Lex is Data:
  Lex{mode: Mode, buf: List<&2, Char>, toks: List<&2, Tok>}

def classify(c: Char) -> Class:
  match c:
    case '[':
      CPunct{TOpenArr{}}
    case ']':
      CPunct{TCloseArr{}}
    case '{':
      CPunct{TOpenObj{}}
    case '}':
      CPunct{TCloseObj{}}
    case ':':
      CPunct{TColon{}}
    case ',':
      CPunct{TComma{}}
    case '"':
      CQuote{}
    case '\\':
      CBack{}
    case ' ':
      CSpace{}
    case '\n':
      CSpace{}
    case '\r':
      CSpace{}
    case '\t':
      CSpace{}
    case _:
      COther{}

def text(buf: List<&2, Char>) -> String:
  String.from_list(List.reverse(&2, Char, buf))

# the char an escape stands for; an unknown escape stands for itself
def unescape(c: Char) -> Char:
  match c:
    case 'n':
      '\n'
    case 'r':
      '\r'
    case 't':
      '\t'
    case 'b':
      Char.from_u32(8)
    case 'f':
      Char.from_u32(12)
    case other:
      other

def hex(c: Char) -> U32:
  +x = Char.to_u32(c)
  Bool.pick(U32, U32.is_le(x, 57), (x - 48 : U32),
    Bool.pick(U32, U32.is_ge(x, 97), (x - 87 : U32), (x - 55 : U32)))

def escape(c: Char, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  match c:
    case 'u':
      Lex{Uni{3n, 0}, buf, toks}
    case other:
      Lex{Str{}, unescape(other) <> buf, toks}

def unicode(left: Nat, acc: U32, c: Char, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  match left:
    case 0n:
      Lex{Str{}, Char.from_u32((acc * 16 + hex(c) : U32)) <> buf, toks}
    case 1n+p:
      Lex{Uni{p, (acc * 16 + hex(c) : U32)}, buf, toks}

def step(mode: Mode, cls: Class, c: Char, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  match mode cls:
    case Idle{} CPunct{t}:
      Lex{Idle{}, [], t <> toks}
    case Idle{} CQuote{}:
      Lex{Str{}, [], toks}
    case Idle{} CSpace{}:
      Lex{Idle{}, [], toks}
    case Idle{} CBack{}:
      Lex{Idle{}, [], TBad{} <> toks}
    case Idle{} COther{}:
      Lex{Word{}, [c], toks}
    case Word{} CPunct{t}:
      Lex{Idle{}, [], t <> TWord{text(buf)} <> toks}
    case Word{} CQuote{}:
      Lex{Str{}, [], TWord{text(buf)} <> toks}
    case Word{} CSpace{}:
      Lex{Idle{}, [], TWord{text(buf)} <> toks}
    case Word{} CBack{}:
      Lex{Idle{}, [], TBad{} <> toks}
    case Word{} COther{}:
      Lex{Word{}, c <> buf, toks}
    case Str{} CQuote{}:
      Lex{Idle{}, [], TStr{text(buf)} <> toks}
    case Str{} CBack{}:
      Lex{Esc{}, buf, toks}
    case Str{} other:
      Lex{Str{}, c <> buf, toks}
    case Esc{} other:
      escape(c, buf, toks)
    case Uni{left, acc} other:
      unicode(left, acc, c, buf, toks)

def feed(+c: Char, st: Lex) -> Lex:
  Lex{mode, buf, toks} = st
  step(mode, classify(c), c, buf, toks)

def run(cs: List<&2, Char>, st: Lex) -> Lex:
  match cs:
    case Nil{}:
      st
    case Con{c, t}:
      run(t, feed(c, st))

# the tokens, in order; text that ends inside a string ends in TBad
def finish(st: Lex) -> List<&2, Tok>:
  Lex{mode, buf, toks} = st
  match mode:
    case Idle{}:
      List.reverse(&2, Tok, toks)
    case Word{}:
      List.reverse(&2, Tok, TWord{text(buf)} <> toks)
    case other:
      List.reverse(&2, Tok, TBad{} <> toks)

def tokens(s: String) -> List<&2, Tok>:
  finish(run(String.to_list(s), Lex{Idle{}, [], []}))
