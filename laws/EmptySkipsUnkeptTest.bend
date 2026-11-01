# `empty` reports nothing for a length test whose x is not read after it in
# its group: one whose group reads no name after it (x is dropped there, and
# on the native lane freeing a list the program never walked costs more than
# the walk the test would have made), one that reads x only before it, and
# one outside any group (bound by a let). Every token at line l, column c
# (laws/defs/EmptyTests.bend).
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/syntax/bind.bend as Bind
import ../src/paths.bend as Paths
import ../src/src.bend as Src
import ../src/syntax/tree.bend as Tree
import ../src/syntax/outline.bend as Outline
import ../src/rules/suspicious/empty.bend as Empty
import ./defs/EmptyTests.bend as D1

# LAW: empty skips a List.length test whose group reads no name after it
law empty_skips_list_dropped:
  for +path: String
  for e: {Paths.is_law_file(path) == False{} : Bool}
  for +x: String
  for +l: U32
  for +c: U32
  for text: String
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Empty.check(Src.Src{path, text, D1.empty.dropped(D1.empty.list_test(x, l, c), l, c),
    tree, bound, items})) == 0n : Nat}

# LAW: empty skips a String.length test whose group reads no name after it
law empty_skips_string_dropped:
  for +path: String
  for e: {Paths.is_law_file(path) == False{} : Bool}
  for +x: String
  for +l: U32
  for +c: U32
  for text: String
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Empty.check(Src.Src{path, text, D1.empty.dropped(D1.empty.str_test(x, l, c), l, c),
    tree, bound, items})) == 0n : Nat}

# LAW: empty skips a List.length test whose x is read only before it
law empty_skips_list_before:
  for +path: String
  for e: {Paths.is_law_file(path) == False{} : Bool}
  for +x: String
  for +l: U32
  for +c: U32
  for text: String
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Empty.check(Src.Src{path, text, D1.empty.before(D1.empty.list_test(x, l, c), x, l, c),
    tree, bound, items})) == 0n : Nat}

# LAW: empty skips a String.length test whose x is read only before it
law empty_skips_string_before:
  for +path: String
  for e: {Paths.is_law_file(path) == False{} : Bool}
  for +x: String
  for +l: U32
  for +c: U32
  for text: String
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Empty.check(Src.Src{path, text, D1.empty.before(D1.empty.str_test(x, l, c), x, l, c),
    tree, bound, items})) == 0n : Nat}

# LAW: empty skips a List.length test outside any group
law empty_skips_list_bare:
  for +path: String
  for e: {Paths.is_law_file(path) == False{} : Bool}
  for +x: String
  for +l: U32
  for +c: U32
  for text: String
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Empty.check(Src.Src{path, text, D1.empty.bare(D1.empty.list_test(x, l, c), x, l, c),
    tree, bound, items})) == 0n : Nat}

# LAW: empty skips a String.length test outside any group
law empty_skips_string_bare:
  for +path: String
  for e: {Paths.is_law_file(path) == False{} : Bool}
  for +x: String
  for +l: U32
  for +c: U32
  for text: String
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Empty.check(Src.Src{path, text, D1.empty.bare(D1.empty.str_test(x, l, c), x, l, c),
    tree, bound, items})) == 0n : Nat}
