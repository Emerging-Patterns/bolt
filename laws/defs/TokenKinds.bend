# the lexer's token kinds as law vocabulary: whether a kind is one of a list
# of kinds. bolt never calls any of it
import Base
import ../../src/syntax/lex.bend as Lex

# a kind's place in the lexer's list of kinds
def kinds.rank(kk: Lex.TokKind) -> U32:
  match kk:
    case Lex.TName{}:
      0
    case Lex.TUpper{}:
      1
    case Lex.TDotted{}:
      2
    case Lex.TWild{}:
      3
    case Lex.TKey{}:
      4
    case Lex.TNum{}:
      5
    case Lex.TStr{}:
      6
    case Lex.TChar{}:
      7
    case Lex.TComment{}:
      8
    case Lex.TSpace{}:
      9
    case Lex.TNewline{}:
      10
    case Lex.TOp{}:
      11
    case Lex.TColon{}:
      12
    case Lex.TEq{}:
      13
    case Lex.TBind{}:
      14
    case Lex.TArrow{}:
      15
    case Lex.TLam{}:
      16
    case Lex.TAll{}:
      17
    case Lex.TAmp{}:
      18
    case Lex.TOpen{}:
      19
    case Lex.TClose{}:
      20
    case Lex.TComma{}:
      21

# are two kinds the same kind?
def kinds.same(aa: Lex.TokKind, bb: Lex.TokKind) -> Bool:
  U32.is_eq(kinds.rank(aa), kinds.rank(bb))

# is a kind one of these?
def kinds.among(+kk: Lex.TokKind, ks: List<&2, Lex.TokKind>) -> Bool:
  match ks:
    case Nil{}:
      False{}
    case Con{k, rest}:
      Bool.or(kinds.same(kk, k), kinds.among(kk, rest))
