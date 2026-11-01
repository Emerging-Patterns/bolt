# the tokens of the tests `empty` reads, as the lexer makes them, every token
# at line l, column c: the laws about `empty` build their sources from these
import Base
import ../../src/syntax/lex.bend as Lex

# `Nat.is_eq(List.length(&2, U32, x), 0n)`
def empty.list_test(+xx: String, +ll: U32, +cc: U32) -> List<&2, Lex.Tok>:
  [Lex.Tok{Lex.TDotted{}, "Nat.is_eq", ll, cc}, Lex.Tok{Lex.TOpen{}, "(", ll, cc},
   Lex.Tok{Lex.TDotted{}, "List.length", ll, cc}, Lex.Tok{Lex.TOpen{}, "(", ll, cc},
   Lex.Tok{Lex.TAmp{}, "&", ll, cc}, Lex.Tok{Lex.TNum{}, "2", ll, cc}, Lex.Tok{Lex.TComma{}, ",", ll, cc},
   Lex.Tok{Lex.TUpper{}, "U32", ll, cc}, Lex.Tok{Lex.TComma{}, ",", ll, cc},
   Lex.Tok{Lex.TName{}, xx, ll, cc}, Lex.Tok{Lex.TClose{}, ")", ll, cc},
   Lex.Tok{Lex.TComma{}, ",", ll, cc}, Lex.Tok{Lex.TNum{}, "0n", ll, cc}, Lex.Tok{Lex.TClose{}, ")", ll, cc}]

# `Nat.is_eq(String.length(x), 0n)`
def empty.str_test(+xx: String, +ll: U32, +cc: U32) -> List<&2, Lex.Tok>:
  [Lex.Tok{Lex.TDotted{}, "Nat.is_eq", ll, cc}, Lex.Tok{Lex.TOpen{}, "(", ll, cc},
   Lex.Tok{Lex.TDotted{}, "String.length", ll, cc}, Lex.Tok{Lex.TOpen{}, "(", ll, cc},
   Lex.Tok{Lex.TName{}, xx, ll, cc}, Lex.Tok{Lex.TClose{}, ")", ll, cc},
   Lex.Tok{Lex.TComma{}, ",", ll, cc}, Lex.Tok{Lex.TNum{}, "0n", ll, cc}, Lex.Tok{Lex.TClose{}, ")", ll, cc}]

# a test as the first argument of a call whose next argument is x: `(`, the
# test, `,`, x and `)`
def empty.kept(test: List<&2, Lex.Tok>, +xx: String, +ll: U32, +cc: U32) -> List<&2, Lex.Tok>:
  Lex.Tok{Lex.TOpen{}, "(", ll, cc} <> List.append(&2, Lex.Tok, test,
    [Lex.Tok{Lex.TComma{}, ",", ll, cc}, Lex.Tok{Lex.TName{}, xx, ll, cc}, Lex.Tok{Lex.TClose{}, ")", ll, cc}])

# a test as the first argument of a call whose next argument is no name:
# `(`, the test, `,`, `1` and `)`
def empty.dropped(test: List<&2, Lex.Tok>, +ll: U32, +cc: U32) -> List<&2, Lex.Tok>:
  Lex.Tok{Lex.TOpen{}, "(", ll, cc} <> List.append(&2, Lex.Tok, test,
    [Lex.Tok{Lex.TComma{}, ",", ll, cc}, Lex.Tok{Lex.TNum{}, "1", ll, cc}, Lex.Tok{Lex.TClose{}, ")", ll, cc}])

# a test as the last argument of a call whose first is x: `(`, x, `,`, the
# test and `)`
def empty.before(test: List<&2, Lex.Tok>, +xx: String, +ll: U32, +cc: U32) -> List<&2, Lex.Tok>:
  Lex.Tok{Lex.TOpen{}, "(", ll, cc} <> Lex.Tok{Lex.TName{}, xx, ll, cc} <> Lex.Tok{Lex.TComma{}, ",", ll, cc}
    <> List.append(&2, Lex.Tok, test, [Lex.Tok{Lex.TClose{}, ")", ll, cc}])

# a test bound by a let, then x: `v`, `=`, the test and x
def empty.bare(test: List<&2, Lex.Tok>, +xx: String, +ll: U32, +cc: U32) -> List<&2, Lex.Tok>:
  Lex.Tok{Lex.TName{}, "v", ll, cc} <> Lex.Tok{Lex.TEq{}, "=", ll, cc}
    <> List.append(&2, Lex.Tok, test, [Lex.Tok{Lex.TName{}, xx, ll, cc}])

# the tokens after the head of a law: `law`, `n` and `:`
def empty.in_law(+ts: List<&2, Lex.Tok>, +ll: U32, +cc: U32) -> List<&2, Lex.Tok>:
  Lex.Tok{Lex.TKey{}, "law", ll, cc} <> Lex.Tok{Lex.TName{}, "n", ll, cc} <> Lex.Tok{Lex.TColon{}, ":", ll, cc} <> ts

# the tokens after the head of a def with no type, which fills a law:
# `def f(s):`
def empty.in_untyped(+ts: List<&2, Lex.Tok>, +ll: U32, +cc: U32) -> List<&2, Lex.Tok>:
  Lex.Tok{Lex.TKey{}, "def", ll, cc} <> Lex.Tok{Lex.TName{}, "f", ll, cc} <> Lex.Tok{Lex.TOpen{}, "(", ll, cc}
    <> Lex.Tok{Lex.TName{}, "s", ll, cc} <> Lex.Tok{Lex.TClose{}, ")", ll, cc} <> Lex.Tok{Lex.TColon{}, ":", ll, cc} <> ts

# the tokens after the head of a def that returns a proof: `def f() -> {} :`
def empty.in_proof(+ts: List<&2, Lex.Tok>, +ll: U32, +cc: U32) -> List<&2, Lex.Tok>:
  Lex.Tok{Lex.TKey{}, "def", ll, cc} <> Lex.Tok{Lex.TName{}, "f", ll, cc} <> Lex.Tok{Lex.TOpen{}, "(", ll, cc}
    <> Lex.Tok{Lex.TClose{}, ")", ll, cc} <> Lex.Tok{Lex.TArrow{}, "->", ll, cc} <> Lex.Tok{Lex.TOpen{}, "{", ll, cc}
    <> Lex.Tok{Lex.TClose{}, "}", ll, cc} <> Lex.Tok{Lex.TColon{}, ":", ll, cc} <> ts

# the tokens after the head of a def that runs: `def f() -> U32:`
def empty.in_typed(+ts: List<&2, Lex.Tok>, +ll: U32, +cc: U32) -> List<&2, Lex.Tok>:
  Lex.Tok{Lex.TKey{}, "def", ll, cc} <> Lex.Tok{Lex.TName{}, "f", ll, cc} <> Lex.Tok{Lex.TOpen{}, "(", ll, cc}
    <> Lex.Tok{Lex.TClose{}, ")", ll, cc} <> Lex.Tok{Lex.TArrow{}, "->", ll, cc} <> Lex.Tok{Lex.TUpper{}, "U32", ll, cc}
    <> Lex.Tok{Lex.TColon{}, ":", ll, cc} <> ts
