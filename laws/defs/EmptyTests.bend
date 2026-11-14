# the tokens of the tests `empty` reads, as the lexer makes them, every token
# at line l, column c: the laws about `empty` build their sources from these
import Base
import ../../src/syntax/lex.bend as Lex

# `Nat.is_eq(List.length(&2, U32, x), 0n)`
def empty.list_test(+x: String, +l: U32, +c: U32) -> List<&2, Lex.Tok>:
  [Lex.Tok{Lex.TDotted{}, "Nat.is_eq", l, c}, Lex.Tok{Lex.TOpen{}, "(", l, c},
   Lex.Tok{Lex.TDotted{}, "List.length", l, c}, Lex.Tok{Lex.TOpen{}, "(", l, c},
   Lex.Tok{Lex.TAmp{}, "&", l, c}, Lex.Tok{Lex.TNum{}, "2", l, c}, Lex.Tok{Lex.TComma{}, ",", l, c},
   Lex.Tok{Lex.TUpper{}, "U32", l, c}, Lex.Tok{Lex.TComma{}, ",", l, c},
   Lex.Tok{Lex.TName{}, x, l, c}, Lex.Tok{Lex.TClose{}, ")", l, c},
   Lex.Tok{Lex.TComma{}, ",", l, c}, Lex.Tok{Lex.TNum{}, "0n", l, c}, Lex.Tok{Lex.TClose{}, ")", l, c}]

# `Nat.is_eq(String.length(x), 0n)`
def empty.str_test(+x: String, +l: U32, +c: U32) -> List<&2, Lex.Tok>:
  [Lex.Tok{Lex.TDotted{}, "Nat.is_eq", l, c}, Lex.Tok{Lex.TOpen{}, "(", l, c},
   Lex.Tok{Lex.TDotted{}, "String.length", l, c}, Lex.Tok{Lex.TOpen{}, "(", l, c},
   Lex.Tok{Lex.TName{}, x, l, c}, Lex.Tok{Lex.TClose{}, ")", l, c},
   Lex.Tok{Lex.TComma{}, ",", l, c}, Lex.Tok{Lex.TNum{}, "0n", l, c}, Lex.Tok{Lex.TClose{}, ")", l, c}]

# a test as the first argument of a call whose next argument is x: `(`, the
# test, `,`, x and `)`
def empty.kept(test: List<&2, Lex.Tok>, +x: String, +l: U32, +c: U32) -> List<&2, Lex.Tok>:
  Lex.Tok{Lex.TOpen{}, "(", l, c} <> List.append(&2, Lex.Tok, test,
    [Lex.Tok{Lex.TComma{}, ",", l, c}, Lex.Tok{Lex.TName{}, x, l, c}, Lex.Tok{Lex.TClose{}, ")", l, c}])

# a test as the first argument of a call whose next argument is no name:
# `(`, the test, `,`, `1` and `)`
def empty.dropped(test: List<&2, Lex.Tok>, +l: U32, +c: U32) -> List<&2, Lex.Tok>:
  Lex.Tok{Lex.TOpen{}, "(", l, c} <> List.append(&2, Lex.Tok, test,
    [Lex.Tok{Lex.TComma{}, ",", l, c}, Lex.Tok{Lex.TNum{}, "1", l, c}, Lex.Tok{Lex.TClose{}, ")", l, c}])

# a test as the last argument of a call whose first is x: `(`, x, `,`, the
# test and `)`
def empty.before(test: List<&2, Lex.Tok>, +x: String, +l: U32, +c: U32) -> List<&2, Lex.Tok>:
  Lex.Tok{Lex.TOpen{}, "(", l, c} <> Lex.Tok{Lex.TName{}, x, l, c} <> Lex.Tok{Lex.TComma{}, ",", l, c}
    <> List.append(&2, Lex.Tok, test, [Lex.Tok{Lex.TClose{}, ")", l, c}])

# a test bound by a let, then x: `v`, `=`, the test and x
def empty.bare(test: List<&2, Lex.Tok>, +x: String, +l: U32, +c: U32) -> List<&2, Lex.Tok>:
  Lex.Tok{Lex.TName{}, "v", l, c} <> Lex.Tok{Lex.TEq{}, "=", l, c}
    <> List.append(&2, Lex.Tok, test, [Lex.Tok{Lex.TName{}, x, l, c}])

# the tokens after the head of a law: `law`, `n` and `:`
def empty.in_law(+ts: List<&2, Lex.Tok>, +l: U32, +c: U32) -> List<&2, Lex.Tok>:
  Lex.Tok{Lex.TKey{}, "law", l, c} <> Lex.Tok{Lex.TName{}, "n", l, c} <> Lex.Tok{Lex.TColon{}, ":", l, c} <> ts

# the tokens after the head of a def with no type, which fills a law:
# `def f(s):`
def empty.in_untyped(+ts: List<&2, Lex.Tok>, +l: U32, +c: U32) -> List<&2, Lex.Tok>:
  Lex.Tok{Lex.TKey{}, "def", l, c} <> Lex.Tok{Lex.TName{}, "f", l, c} <> Lex.Tok{Lex.TOpen{}, "(", l, c}
    <> Lex.Tok{Lex.TName{}, "s", l, c} <> Lex.Tok{Lex.TClose{}, ")", l, c} <> Lex.Tok{Lex.TColon{}, ":", l, c} <> ts

# the tokens after the head of a def that returns a proof: `def f() -> {} :`
def empty.in_proof(+ts: List<&2, Lex.Tok>, +l: U32, +c: U32) -> List<&2, Lex.Tok>:
  Lex.Tok{Lex.TKey{}, "def", l, c} <> Lex.Tok{Lex.TName{}, "f", l, c} <> Lex.Tok{Lex.TOpen{}, "(", l, c}
    <> Lex.Tok{Lex.TClose{}, ")", l, c} <> Lex.Tok{Lex.TArrow{}, "->", l, c} <> Lex.Tok{Lex.TOpen{}, "{", l, c}
    <> Lex.Tok{Lex.TClose{}, "}", l, c} <> Lex.Tok{Lex.TColon{}, ":", l, c} <> ts

# the tokens after the head of a def that runs: `def f() -> U32:`
def empty.in_typed(+ts: List<&2, Lex.Tok>, +l: U32, +c: U32) -> List<&2, Lex.Tok>:
  Lex.Tok{Lex.TKey{}, "def", l, c} <> Lex.Tok{Lex.TName{}, "f", l, c} <> Lex.Tok{Lex.TOpen{}, "(", l, c}
    <> Lex.Tok{Lex.TClose{}, ")", l, c} <> Lex.Tok{Lex.TArrow{}, "->", l, c} <> Lex.Tok{Lex.TUpper{}, "U32", l, c}
    <> Lex.Tok{Lex.TColon{}, ":", l, c} <> ts
