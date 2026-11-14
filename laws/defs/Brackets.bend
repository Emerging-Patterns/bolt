# the four brackets as law vocabulary: the text each opens and closes with,
# and a call through each. bolt never calls any of it
import Base
import ../../src/syntax/lex.bend as Lex
import ../../src/syntax/tree.bend as Tree

# one of the four brackets
type Bracket is Data:
  BParen{}
  BSquare{}
  BBrace{}
  BAngle{}

# the char a bracket opens with
def br.open_char(b: Bracket) -> Char:
  match b:
    case BParen{}:
      '('
    case BSquare{}:
      '['
    case BBrace{}:
      '{'
    case BAngle{}:
      '<'

# the char a bracket closes with
def br.close_char(b: Bracket) -> Char:
  match b:
    case BParen{}:
      ')'
    case BSquare{}:
      ']'
    case BBrace{}:
      '}'
    case BAngle{}:
      '>'

# the text a bracket opens with
def br.open(b: Bracket) -> String:
  String.from_list([br.open_char(b)])

# the text a bracket closes with
def br.close(b: Bracket) -> String:
  String.from_list([br.close_char(b)])

# is it the round bracket?
def br.is_paren(b: Bracket) -> Bool:
  match b:
    case BParen{}:
      True{}
    case other:
      False{}

# the callee `f`, as the token a rule reports
def br.callee() -> Lex.Tok:
  Lex.Tok{Lex.TName{}, "f", 0, 0}

# `f` then a closed group opened by this bracket: `f(..)`, `f[..]`, `f{..}`, `f<..>`
def br.call(+b: Bracket) -> Tree.Node:
  Tree.NCons{Tree.Leaf{br.callee()},
    Tree.NCons{Tree.Group{Lex.Tok{Lex.TOpen{}, br.open(b), 0, 1}, Tree.NNil{},
      Some{Lex.Tok{Lex.TClose{}, br.close(b), 0, 2}}}, Tree.NNil{}}}

# `f(..)` inside a group this bracket opens: `(f(..))`, `[f(..)]`, ..
def br.wrapped(+b: Bracket) -> Tree.Node:
  Tree.NCons{Tree.Group{Lex.Tok{Lex.TOpen{}, br.open(b), 0, 0}, br.call(BParen{}),
    Some{Lex.Tok{Lex.TClose{}, br.close(b), 0, 3}}}, Tree.NNil{}}

# a call through this bracket inside one pair of round brackets: `(f(..))`, `(f[..])`, ..
def br.inside(+b: Bracket) -> Tree.Node:
  Tree.NCons{Tree.Group{Lex.Tok{Lex.TOpen{}, "(", 0, 0}, br.call(b),
    Some{Lex.Tok{Lex.TClose{}, ")", 0, 3}}}, Tree.NNil{}}
