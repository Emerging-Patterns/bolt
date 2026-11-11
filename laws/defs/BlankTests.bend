# the tokens of the tests `blank` reads, as the lexer makes them, every token
# at line l, column c: the laws about `blank` build their sources from these
import Base
import ../../src/syntax/lex.bend as Lex

# `String.eq(` and what follows it
def blank.call(+ll: U32, +cc: U32, args: List<&2, Lex.Tok>) -> List<&2, Lex.Tok>:
  Lex.Tok{Lex.TDotted{}, "String.eq", ll, cc} <> Lex.Tok{Lex.TOpen{}, "(", ll, cc} <> args

# `String.eq(x, lit)`, lit a string literal's text with its quotes
def blank.second(xx: String, lit: String, +ll: U32, +cc: U32) -> List<&2, Lex.Tok>:
  blank.call(ll, cc, [Lex.Tok{Lex.TName{}, xx, ll, cc}, Lex.Tok{Lex.TComma{}, ",", ll, cc},
    Lex.Tok{Lex.TStr{}, lit, ll, cc}, Lex.Tok{Lex.TClose{}, ")", ll, cc}])

# `String.eq("", x)`
def blank.first(xx: String, +ll: U32, +cc: U32) -> List<&2, Lex.Tok>:
  blank.call(ll, cc, [Lex.Tok{Lex.TStr{}, "\"\"", ll, cc}, Lex.Tok{Lex.TComma{}, ",", ll, cc},
    Lex.Tok{Lex.TName{}, xx, ll, cc}, Lex.Tok{Lex.TClose{}, ")", ll, cc}])

# `String.eq(String.trim(x), "")`: the first argument a call
def blank.deep(xx: String, +ll: U32, +cc: U32) -> List<&2, Lex.Tok>:
  blank.call(ll, cc, [Lex.Tok{Lex.TDotted{}, "String.trim", ll, cc}, Lex.Tok{Lex.TOpen{}, "(", ll, cc},
    Lex.Tok{Lex.TName{}, xx, ll, cc}, Lex.Tok{Lex.TClose{}, ")", ll, cc}, Lex.Tok{Lex.TComma{}, ",", ll, cc},
    Lex.Tok{Lex.TStr{}, "\"\"", ll, cc}, Lex.Tok{Lex.TClose{}, ")", ll, cc}])

# `String.eq(f(x, ""), x)`: the literal an argument of a call inside
def blank.inner(+xx: String, +ll: U32, +cc: U32) -> List<&2, Lex.Tok>:
  blank.call(ll, cc, [Lex.Tok{Lex.TName{}, "f", ll, cc}, Lex.Tok{Lex.TOpen{}, "(", ll, cc},
    Lex.Tok{Lex.TName{}, xx, ll, cc}, Lex.Tok{Lex.TComma{}, ",", ll, cc}, Lex.Tok{Lex.TStr{}, "\"\"", ll, cc},
    Lex.Tok{Lex.TClose{}, ")", ll, cc}, Lex.Tok{Lex.TComma{}, ",", ll, cc}, Lex.Tok{Lex.TName{}, xx, ll, cc},
    Lex.Tok{Lex.TClose{}, ")", ll, cc}])

# `M.eq(x, "")`: a qualified name that is not `String.eq`
def blank.aliased(xx: String, +ll: U32, +cc: U32) -> List<&2, Lex.Tok>:
  [Lex.Tok{Lex.TDotted{}, "M.eq", ll, cc}, Lex.Tok{Lex.TOpen{}, "(", ll, cc}, Lex.Tok{Lex.TName{}, xx, ll, cc},
   Lex.Tok{Lex.TComma{}, ",", ll, cc}, Lex.Tok{Lex.TStr{}, "\"\"", ll, cc}, Lex.Tok{Lex.TClose{}, ")", ll, cc}]

# `String.eq(7, "")`: the other argument a number, no name
def blank.number(num: String, +ll: U32, +cc: U32) -> List<&2, Lex.Tok>:
  blank.call(ll, cc, [Lex.Tok{Lex.TNum{}, num, ll, cc}, Lex.Tok{Lex.TComma{}, ",", ll, cc},
    Lex.Tok{Lex.TStr{}, "\"\"", ll, cc}, Lex.Tok{Lex.TClose{}, ")", ll, cc}])

# `String.eq(x ++ "")`: one argument, no comma before the literal
def blank.joined(xx: String, +ll: U32, +cc: U32) -> List<&2, Lex.Tok>:
  blank.call(ll, cc, [Lex.Tok{Lex.TName{}, xx, ll, cc}, Lex.Tok{Lex.TOp{}, "++", ll, cc},
    Lex.Tok{Lex.TStr{}, "\"\"", ll, cc}, Lex.Tok{Lex.TClose{}, ")", ll, cc}])

# `String.eq(x, "" ++ x)`: the literal only the start of the second argument
def blank.longer(+xx: String, +ll: U32, +cc: U32) -> List<&2, Lex.Tok>:
  blank.call(ll, cc, [Lex.Tok{Lex.TName{}, xx, ll, cc}, Lex.Tok{Lex.TComma{}, ",", ll, cc},
    Lex.Tok{Lex.TStr{}, "\"\"", ll, cc}, Lex.Tok{Lex.TOp{}, "++", ll, cc}, Lex.Tok{Lex.TName{}, xx, ll, cc},
    Lex.Tok{Lex.TClose{}, ")", ll, cc}])
