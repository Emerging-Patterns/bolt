# bolt/rules/tokens: helpers the token rules share (put, escape, nat, strings,
# twice, arms): significant tokens, literal kinds, Nat literals, case
# patterns, and a name's uses under a node.
import Base
import ../../lazy/lazy.bend as Lazy
import ../../syntax/lex.bend as Lex
import ../../syntax/tree.bend as Tree

# the tokens without space, newlines and comments
def sig(toks: List<&2, Lex.Tok>) -> List<&2, Lex.Tok>:
  match toks:
    case Nil{}:
      Nil{}
    case Con{Lex.Tok{+k, t, l, c}, rest}:
      +more = sig(rest)
      Bool.pick(List<&2, Lex.Tok>, Lex.significant(k), Lex.Tok{k, t, l, c} <> more, more)

# a text cut to its first char
def code.cut(tt: String) -> String:
  match tt:
    case SNil{}:
      SNil{}
    case SCon{h, _t}:
      SCon{h, SNil{}}

# a string literal cut to its opening quote; any other token as it is
def code.tok(tk: Lex.Tok) -> Lex.Tok:
  match tk:
    case Lex.Tok{+k, +t, l, c}:
      Lex.Tok{k, Bool.pick(String, Lex.is_str(k), code.cut(t), t), l, c}

# the tokens, each string literal cut to its opening quote
def code.toks(ts: List<&2, Lex.Tok>) -> List<&2, Lex.Tok>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      code.tok(h) <> code.toks(t)

# a text with each string literal cut to its opening quote: what of it is
# code, as the lexer reads it
def code(+tt: String) -> String:
  Lex.text(code.toks(Lex.tokens(tt)))

# a number, a char or a string literal?
def is_lit(kk: Lex.TokKind) -> Bool:
  match kk:
    case Lex.TNum{}:
      True{}
    case Lex.TChar{}:
      True{}
    case Lex.TStr{}:
      True{}
    case other:
      False{}

# digits, then one final `n`: a Nat literal's chars
def nat_ok(cs: List<&2, Char>) -> Bool:
  match cs:
    case Con{'n', Nil{}}:
      True{}
    case Con{+c, t}:
      Lazy.and_then(Char.is_digit(c), _u => nat_ok(t))
    case Nil{}:
      False{}

# the text without its last char (a Nat literal's digits)
def stem(+tt: String) -> String:
  String.take(tt, Nat.sub(String.length(tt), 1n))

# a Nat literal's value (`12n` is 12); none for anything else or past U32
def nat_value(+tt: String) -> Maybe<&2, U32>:
  Bool.pick(Maybe<&2, U32>, nat_ok(String.to_list(tt)), U32.read(stem(tt)), None{})

# a text's width in chars
def width(tt: String) -> U32:
  U32.from_nat(String.length(tt))

# is the first node the keyword?
def keyword(nn: Tree.Node, +word: String) -> Bool:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TKey{}, +t, l, c}}, rest}:
      String.eq(t, word)
    case other:
      False{}

# a case statement's pattern (its tokens after `case`, the colon and an
# inline body included)
def pattern(kids: Tree.Node) -> Tree.Node:
  match kids:
    case Tree.NCons{h, rest}:
      rest
    case other:
      other
