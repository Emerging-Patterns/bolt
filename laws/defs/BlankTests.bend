# the tokens of the tests `blank` reads, as the lexer makes them, every token
# at line l, column c: the laws about `blank` build their sources from these
import Base
import ../../src/syntax/lex.bend as Lex

# `String.eq(` and what follows it
def blank.call(+l: U32, +c: U32, args: List<&2, Lex.Tok>) -> List<&2, Lex.Tok>:
  Lex.Tok{Lex.TDotted{}, "String.eq", l, c} <> Lex.Tok{Lex.TOpen{}, "(", l, c} <> args

# `String.eq(x, lit)`, lit a string literal's text with its quotes
def blank.second(x: String, lit: String, +l: U32, +c: U32) -> List<&2, Lex.Tok>:
  blank.call(l, c, [Lex.Tok{Lex.TName{}, x, l, c}, Lex.Tok{Lex.TComma{}, ",", l, c},
    Lex.Tok{Lex.TStr{}, lit, l, c}, Lex.Tok{Lex.TClose{}, ")", l, c}])

# `String.eq("", x)`
def blank.first(x: String, +l: U32, +c: U32) -> List<&2, Lex.Tok>:
  blank.call(l, c, [Lex.Tok{Lex.TStr{}, "\"\"", l, c}, Lex.Tok{Lex.TComma{}, ",", l, c},
    Lex.Tok{Lex.TName{}, x, l, c}, Lex.Tok{Lex.TClose{}, ")", l, c}])

# `String.eq(String.trim(x), "")`: the first argument a call
def blank.deep(x: String, +l: U32, +c: U32) -> List<&2, Lex.Tok>:
  blank.call(l, c, [Lex.Tok{Lex.TDotted{}, "String.trim", l, c}, Lex.Tok{Lex.TOpen{}, "(", l, c},
    Lex.Tok{Lex.TName{}, x, l, c}, Lex.Tok{Lex.TClose{}, ")", l, c}, Lex.Tok{Lex.TComma{}, ",", l, c},
    Lex.Tok{Lex.TStr{}, "\"\"", l, c}, Lex.Tok{Lex.TClose{}, ")", l, c}])

# `String.eq(f(x, ""), x)`: the literal an argument of a call inside
def blank.inner(+x: String, +l: U32, +c: U32) -> List<&2, Lex.Tok>:
  blank.call(l, c, [Lex.Tok{Lex.TName{}, "f", l, c}, Lex.Tok{Lex.TOpen{}, "(", l, c},
    Lex.Tok{Lex.TName{}, x, l, c}, Lex.Tok{Lex.TComma{}, ",", l, c}, Lex.Tok{Lex.TStr{}, "\"\"", l, c},
    Lex.Tok{Lex.TClose{}, ")", l, c}, Lex.Tok{Lex.TComma{}, ",", l, c}, Lex.Tok{Lex.TName{}, x, l, c},
    Lex.Tok{Lex.TClose{}, ")", l, c}])

# `M.eq(x, "")`: a qualified name that is not `String.eq`
def blank.aliased(x: String, +l: U32, +c: U32) -> List<&2, Lex.Tok>:
  [Lex.Tok{Lex.TDotted{}, "M.eq", l, c}, Lex.Tok{Lex.TOpen{}, "(", l, c}, Lex.Tok{Lex.TName{}, x, l, c},
   Lex.Tok{Lex.TComma{}, ",", l, c}, Lex.Tok{Lex.TStr{}, "\"\"", l, c}, Lex.Tok{Lex.TClose{}, ")", l, c}]

# `String.eq(7, "")`: the other argument a number, no name
def blank.number(num: String, +l: U32, +c: U32) -> List<&2, Lex.Tok>:
  blank.call(l, c, [Lex.Tok{Lex.TNum{}, num, l, c}, Lex.Tok{Lex.TComma{}, ",", l, c},
    Lex.Tok{Lex.TStr{}, "\"\"", l, c}, Lex.Tok{Lex.TClose{}, ")", l, c}])

# `String.eq(x ++ "")`: one argument, no comma before the literal
def blank.joined(x: String, +l: U32, +c: U32) -> List<&2, Lex.Tok>:
  blank.call(l, c, [Lex.Tok{Lex.TName{}, x, l, c}, Lex.Tok{Lex.TOp{}, "++", l, c},
    Lex.Tok{Lex.TStr{}, "\"\"", l, c}, Lex.Tok{Lex.TClose{}, ")", l, c}])

# `String.eq(x, "" ++ x)`: the literal only the start of the second argument
def blank.longer(+x: String, +l: U32, +c: U32) -> List<&2, Lex.Tok>:
  blank.call(l, c, [Lex.Tok{Lex.TName{}, x, l, c}, Lex.Tok{Lex.TComma{}, ",", l, c},
    Lex.Tok{Lex.TStr{}, "\"\"", l, c}, Lex.Tok{Lex.TOp{}, "++", l, c}, Lex.Tok{Lex.TName{}, x, l, c},
    Lex.Tok{Lex.TClose{}, ")", l, c}])
