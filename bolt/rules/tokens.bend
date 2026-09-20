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

# a number, a char or a string literal?
def is_lit(k: Lex.TokKind) -> Bool:
  match k:
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
def stem(+t: String) -> String:
  String.take(t, Nat.sub(String.length(t), 1n))

# a Nat literal's value (`12n` is 12); none for anything else or past U32
def nat_value(+t: String) -> Maybe<&2, U32>:
  Bool.pick(Maybe<&2, U32>, nat_ok(String.to_list(t)), U32.read(stem(t)), None{})

# a text's width in chars
def width(t: String) -> U32:
  U32.from_nat(String.length(t))

# is the first node the keyword?
def keyword(n: Tree.Node, +word: String) -> Bool:
  match n:
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

# does the name appear anywhere under the node?
def mentions(n: Tree.Node, +name: String) -> Bool:
  match n:
    case Tree.Leaf{Lex.Tok{k, +t, l, c}}:
      String.eq(t, name)
    case Tree.Group{open, kids, close}:
      mentions(kids, name)
    case Tree.Stmt{kind, kids, body}:
      Lazy.or_else(mentions(kids, name), _u => mentions(body, name))
    case Tree.NNil{}:
      False{}
    case Tree.NCons{h, t}:
      Lazy.or_else(mentions(h, name), _u => mentions(t, name))
