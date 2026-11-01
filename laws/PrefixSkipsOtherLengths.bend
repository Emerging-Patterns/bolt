# `prefix` reports nothing for `String.eq(String.take(s, k), lit)` or
# `String.eq(lit, String.take(s, k))`, k a Nat literal and lit a string
# literal, as the lexer gives them, s a name or `String.drop(s, n)`, when k
# is not the literal's length (laws/defs/PrefixLength.bend) in decimal and
# then `n`: `String.eq(String.take(m, 3n), "ERR ")` compares a shorter
# prefix to a longer literal, a different bug that starts_with would not
# fix.
#
# also rests on: laws/PrefixReportsTakeComparedToLiteral.bend
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/syntax/bind.bend as Bind
import ../src/paths.bend as Paths
import ../src/src.bend as Src
import ../src/syntax/tree.bend as Tree
import ../src/syntax/outline.bend as Outline
import ../src/rules/suspicious/prefix.bend as Prefix
import ./defs/PrefixLength.bend as D1

# LAW: prefix reports nothing for a take of a name, then a literal of another length
law prefix_skips_take_first:
  for +path: String
  for e: {Paths.is_law_file(path) == False{} : Bool}
  for +s: String
  for +k: String
  for +lit: String
  for +l: U32
  for +c: U32
  for f: {D1.prefix_fits(k, lit) == False{} : Bool}
  for text: String
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Prefix.check(Src.Src{path, text,
    [Lex.Tok{Lex.TDotted{}, "String.eq", l, c}, Lex.Tok{Lex.TOpen{}, "(", l, c},
     Lex.Tok{Lex.TDotted{}, "String.take", l, c}, Lex.Tok{Lex.TOpen{}, "(", l, c},
     Lex.Tok{Lex.TName{}, s, l, c}, Lex.Tok{Lex.TComma{}, ",", l, c},
     Lex.Tok{Lex.TNum{}, k, l, c}, Lex.Tok{Lex.TClose{}, ")", l, c},
     Lex.Tok{Lex.TComma{}, ",", l, c}, Lex.Tok{Lex.TStr{}, lit, l, c},
     Lex.Tok{Lex.TClose{}, ")", l, c}],
    tree, bound, items})) == 0n : Nat}

# LAW: prefix reports nothing for a literal, then a take of a name of another length
law prefix_skips_literal_first:
  for +path: String
  for e: {Paths.is_law_file(path) == False{} : Bool}
  for +s: String
  for +k: String
  for +lit: String
  for +l: U32
  for +c: U32
  for f: {D1.prefix_fits(k, lit) == False{} : Bool}
  for text: String
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Prefix.check(Src.Src{path, text,
    [Lex.Tok{Lex.TDotted{}, "String.eq", l, c}, Lex.Tok{Lex.TOpen{}, "(", l, c},
     Lex.Tok{Lex.TStr{}, lit, l, c}, Lex.Tok{Lex.TComma{}, ",", l, c},
     Lex.Tok{Lex.TDotted{}, "String.take", l, c}, Lex.Tok{Lex.TOpen{}, "(", l, c},
     Lex.Tok{Lex.TName{}, s, l, c}, Lex.Tok{Lex.TComma{}, ",", l, c},
     Lex.Tok{Lex.TNum{}, k, l, c}, Lex.Tok{Lex.TClose{}, ")", l, c},
     Lex.Tok{Lex.TClose{}, ")", l, c}],
    tree, bound, items})) == 0n : Nat}

# LAW: prefix reports nothing for a take of `String.drop(s, n)`, then a literal of another length
law prefix_skips_drop_take_first:
  for +path: String
  for e: {Paths.is_law_file(path) == False{} : Bool}
  for +s: String
  for +n: String
  for +k: String
  for +lit: String
  for +l: U32
  for +c: U32
  for f: {D1.prefix_fits(k, lit) == False{} : Bool}
  for text: String
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Prefix.check(Src.Src{path, text,
    [Lex.Tok{Lex.TDotted{}, "String.eq", l, c}, Lex.Tok{Lex.TOpen{}, "(", l, c},
     Lex.Tok{Lex.TDotted{}, "String.take", l, c}, Lex.Tok{Lex.TOpen{}, "(", l, c},
     Lex.Tok{Lex.TDotted{}, "String.drop", l, c}, Lex.Tok{Lex.TOpen{}, "(", l, c},
     Lex.Tok{Lex.TName{}, s, l, c}, Lex.Tok{Lex.TComma{}, ",", l, c},
     Lex.Tok{Lex.TNum{}, n, l, c}, Lex.Tok{Lex.TClose{}, ")", l, c},
     Lex.Tok{Lex.TComma{}, ",", l, c}, Lex.Tok{Lex.TNum{}, k, l, c},
     Lex.Tok{Lex.TClose{}, ")", l, c}, Lex.Tok{Lex.TComma{}, ",", l, c},
     Lex.Tok{Lex.TStr{}, lit, l, c}, Lex.Tok{Lex.TClose{}, ")", l, c}],
    tree, bound, items})) == 0n : Nat}

# LAW: prefix reports nothing for a literal, then a take of `String.drop(s, n)` of another length
law prefix_skips_drop_literal_first:
  for +path: String
  for e: {Paths.is_law_file(path) == False{} : Bool}
  for +s: String
  for +n: String
  for +k: String
  for +lit: String
  for +l: U32
  for +c: U32
  for f: {D1.prefix_fits(k, lit) == False{} : Bool}
  for text: String
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Prefix.check(Src.Src{path, text,
    [Lex.Tok{Lex.TDotted{}, "String.eq", l, c}, Lex.Tok{Lex.TOpen{}, "(", l, c},
     Lex.Tok{Lex.TStr{}, lit, l, c}, Lex.Tok{Lex.TComma{}, ",", l, c},
     Lex.Tok{Lex.TDotted{}, "String.take", l, c}, Lex.Tok{Lex.TOpen{}, "(", l, c},
     Lex.Tok{Lex.TDotted{}, "String.drop", l, c}, Lex.Tok{Lex.TOpen{}, "(", l, c},
     Lex.Tok{Lex.TName{}, s, l, c}, Lex.Tok{Lex.TComma{}, ",", l, c},
     Lex.Tok{Lex.TNum{}, n, l, c}, Lex.Tok{Lex.TClose{}, ")", l, c},
     Lex.Tok{Lex.TComma{}, ",", l, c}, Lex.Tok{Lex.TNum{}, k, l, c},
     Lex.Tok{Lex.TClose{}, ")", l, c}, Lex.Tok{Lex.TClose{}, ")", l, c}],
    tree, bound, items})) == 0n : Nat}
