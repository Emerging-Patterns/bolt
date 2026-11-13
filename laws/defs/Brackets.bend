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
def br.open_char(bb: Bracket) -> Char:
  match bb:
    case BParen{}:
      '('
    case BSquare{}:
      '['
    case BBrace{}:
      '{'
    case BAngle{}:
      '<'

# the char a bracket closes with
def br.close_char(bb: Bracket) -> Char:
  match bb:
    case BParen{}:
      ')'
    case BSquare{}:
      ']'
    case BBrace{}:
      '}'
    case BAngle{}:
      '>'

# the text a bracket opens with
def br.open(bb: Bracket) -> String:
  String.from_list([br.open_char(bb)])

# the text a bracket closes with
def br.close(bb: Bracket) -> String:
  String.from_list([br.close_char(bb)])

# is it the round bracket?
def br.is_paren(bb: Bracket) -> Bool:
  match bb:
    case BParen{}:
      True{}
    case other:
      False{}

# the callee `f`, as the token a rule reports
def br.callee() -> Lex.Tok:
  Lex.Tok{Lex.TName{}, "f", 0, 0}

# `f` then a closed group opened by this bracket: `f(..)`, `f[..]`, `f{..}`, `f<..>`
def br.call(+bb: Bracket) -> Tree.Node:
  Tree.NCons{Tree.Leaf{br.callee()},
    Tree.NCons{Tree.Group{Lex.Tok{Lex.TOpen{}, br.open(bb), 0, 1}, Tree.NNil{},
      Some{Lex.Tok{Lex.TClose{}, br.close(bb), 0, 2}}}, Tree.NNil{}}}

# `f(..)` inside a group this bracket opens: `(f(..))`, `[f(..)]`, ..
def br.wrapped(+bb: Bracket) -> Tree.Node:
  Tree.NCons{Tree.Group{Lex.Tok{Lex.TOpen{}, br.open(bb), 0, 0}, br.call(BParen{}),
    Some{Lex.Tok{Lex.TClose{}, br.close(bb), 0, 3}}}, Tree.NNil{}}

# a call through this bracket inside one pair of round brackets: `(f(..))`, `(f[..])`, ..
def br.inside(+bb: Bracket) -> Tree.Node:
  Tree.NCons{Tree.Group{Lex.Tok{Lex.TOpen{}, "(", 0, 0}, br.call(bb),
    Some{Lex.Tok{Lex.TClose{}, ")", 0, 3}}}, Tree.NNil{}}
