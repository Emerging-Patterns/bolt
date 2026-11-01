# `empty` reports `Nat.is_eq(List.length(.., x), 0n)` and
# `Nat.is_eq(String.length(x), 0n)`, once each, outside a LAWS.bend or a
# PROOF.bend, when the test is an argument (here the first, after a `(`) and
# x, a plain name, is read again later in the same group: there the test's
# reference to x is dropped by a count, and List.is_empty or String.is_empty
# gives the same Bool from one cell. Every token at line l, column c
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

# LAW: empty reports a List.length test that is an argument, x read later in its group, once
law empty_reports_list_kept:
  for +path: String
  for e: {Paths.is_law_file(path) == False{} : Bool}
  for +x: String
  for +l: U32
  for +c: U32
  for text: String
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Empty.check(Src.Src{path, text, D1.empty.kept(D1.empty.list_test(x, l, c), x, l, c),
    tree, bound, items})) == 1n : Nat}

# LAW: empty reports a String.length test that is an argument, x read later in its group, once
law empty_reports_string_kept:
  for +path: String
  for e: {Paths.is_law_file(path) == False{} : Bool}
  for +x: String
  for +l: U32
  for +c: U32
  for text: String
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Empty.check(Src.Src{path, text, D1.empty.kept(D1.empty.str_test(x, l, c), x, l, c),
    tree, bound, items})) == 1n : Nat}

# LAW: empty reports a kept test in a def that runs, once
law empty_reports_in_typed_def:
  for +path: String
  for e: {Paths.is_law_file(path) == False{} : Bool}
  for +x: String
  for +l: U32
  for +c: U32
  for text: String
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Empty.check(Src.Src{path, text,
    D1.empty.in_typed(D1.empty.kept(D1.empty.list_test(x, l, c), x, l, c), l, c),
    tree, bound, items})) == 1n : Nat}
