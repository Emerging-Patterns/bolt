# `prefix` reports `String.eq(String.take(s, k), lit)` and
# `String.eq(lit, String.take(s, k))`, k a Nat literal and lit a string
# literal, as the lexer gives them, once each, outside a LAWS.bend or a
# PROOF.bend, when k is the literal's length (laws/defs/PrefixLength.bend)
# in decimal and then `n`: s a name, or an expression of several tokens
# such as `String.drop(s, n)`. `String.eq(String.take(m, 4n), "ERR ")` is
# one finding, and so is `String.eq(String.take(String.drop(m, 4n), 1n),
# "-")`.
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

# LAW: prefix reports a take of a name, then a literal of its length, once
law prefix_reports_take_first:
  for +path: String
  for e: {Paths.is_law_file(path) == False{} : Bool}
  for +s: String
  for +k: String
  for +lit: String
  for +l: U32
  for +c: U32
  for f: {D1.prefix_fits(k, lit) == True{} : Bool}
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
    tree, bound, items})) == 1n : Nat}

# LAW: prefix reports a literal, then a take of a name of its length, once
law prefix_reports_literal_first:
  for +path: String
  for e: {Paths.is_law_file(path) == False{} : Bool}
  for +s: String
  for +k: String
  for +lit: String
  for +l: U32
  for +c: U32
  for f: {D1.prefix_fits(k, lit) == True{} : Bool}
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
    tree, bound, items})) == 1n : Nat}

# LAW: prefix reports a take of `String.drop(s, n)`, then a literal of its length, once
law prefix_reports_drop_take_first:
  for +path: String
  for e: {Paths.is_law_file(path) == False{} : Bool}
  for +s: String
  for +n: String
  for +k: String
  for +lit: String
  for +l: U32
  for +c: U32
  for f: {D1.prefix_fits(k, lit) == True{} : Bool}
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
    tree, bound, items})) == 1n : Nat}

# LAW: prefix reports a literal, then a take of `String.drop(s, n)` of its length, once
law prefix_reports_drop_literal_first:
  for +path: String
  for e: {Paths.is_law_file(path) == False{} : Bool}
  for +s: String
  for +n: String
  for +k: String
  for +lit: String
  for +l: U32
  for +c: U32
  for f: {D1.prefix_fits(k, lit) == True{} : Bool}
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
    tree, bound, items})) == 1n : Nat}
