# `empty` reports nothing in a law, or in a def that is a proof: one written
# with no type (`def f(s):`, which fills the law named f) or one that returns
# a proof (`-> {a == b : T}`). Neither runs, so what a test there costs does
# not matter, and a law states the test as it means it. Every token at line
# l, column c (laws/defs/EmptyTests.bend).
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

# LAW: empty skips a kept test in a law
law empty_skips_in_law:
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
    D1.empty.in_law(D1.empty.kept(D1.empty.list_test(x, l, c), x, l, c), l, c),
    tree, bound, items})) == 0n : Nat}

# LAW: empty skips a kept test in a def with no type
law empty_skips_in_untyped_def:
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
    D1.empty.in_untyped(D1.empty.kept(D1.empty.list_test(x, l, c), x, l, c), l, c),
    tree, bound, items})) == 0n : Nat}

# LAW: empty skips a kept test in a def that returns a proof
law empty_skips_in_proof_def:
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
    D1.empty.in_proof(D1.empty.kept(D1.empty.list_test(x, l, c), x, l, c), l, c),
    tree, bound, items})) == 0n : Nat}
