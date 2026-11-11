# `blank` reports `String.eq(x, "")` and `String.eq("", x)`, x a plain name,
# once each, outside a LAWS.bend or a PROOF.bend: the test asks whether x is
# empty, and String.is_empty says so. A literal of anything else, an
# argument that is a call (there `""` is as often the value a test expects),
# a `""` that is an argument of a call inside, and a name that is not
# `String.eq` are left alone. Every token at line l, column c
# (laws/defs/BlankTests.bend).
#
# also rests on: laws/BlankSkipsProofs.bend, laws/BlankExempt.bend,
# laws/InertBlank.bend
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/syntax/bind.bend as Bind
import ../src/paths.bend as Paths
import ../src/src.bend as Src
import ../src/syntax/tree.bend as Tree
import ../src/syntax/outline.bend as Outline
import ../src/rules/style/blank.bend as Blank
import ./defs/BlankTests.bend as D1
import ./defs/EmptyTests.bend as D2

# LAW: blank reports a String.eq whose second argument is `""`, once
law blank_reports_second:
  for +path: String
  for e: {Paths.is_law_file(path) == False{} : Bool}
  for xx: String
  for +ll: U32
  for +cc: U32
  for text: String
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Blank.check(Src.Src{path, text, D1.blank.second(xx, "\"\"", ll, cc),
    tree, bound, items})) == 1n : Nat}

# LAW: blank reports a String.eq whose first argument is `""`, once
law blank_reports_first:
  for +path: String
  for e: {Paths.is_law_file(path) == False{} : Bool}
  for xx: String
  for +ll: U32
  for +cc: U32
  for text: String
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Blank.check(Src.Src{path, text, D1.blank.first(xx, ll, cc),
    tree, bound, items})) == 1n : Nat}

# LAW: blank reports no String.eq whose other argument is a call
law blank_skips_call:
  for +path: String
  for e: {Paths.is_law_file(path) == False{} : Bool}
  for xx: String
  for +ll: U32
  for +cc: U32
  for text: String
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Blank.check(Src.Src{path, text, D1.blank.deep(xx, ll, cc),
    tree, bound, items})) == 0n : Nat}

# LAW: blank reports the test in a def that runs, once
law blank_reports_in_typed_def:
  for +path: String
  for e: {Paths.is_law_file(path) == False{} : Bool}
  for xx: String
  for +ll: U32
  for +cc: U32
  for text: String
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Blank.check(Src.Src{path, text,
    D2.empty.in_typed(D1.blank.second(xx, "\"\"", ll, cc), ll, cc),
    tree, bound, items})) == 1n : Nat}

# LAW: blank reports no String.eq with a string literal that is not `""`
law blank_skips_other_literal:
  for +path: String
  for e: {Paths.is_law_file(path) == False{} : Bool}
  for xx: String
  for +ll: U32
  for +cc: U32
  for +lit: String
  for ne: {String.eq(lit, "\"\"") == False{} : Bool}
  for text: String
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Blank.check(Src.Src{path, text, D1.blank.second(xx, lit, ll, cc),
    tree, bound, items})) == 0n : Nat}

# LAW: blank reports no String.eq for a `""` that is an argument of a call
# inside it
law blank_skips_inner:
  for +path: String
  for e: {Paths.is_law_file(path) == False{} : Bool}
  for +xx: String
  for +ll: U32
  for +cc: U32
  for text: String
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Blank.check(Src.Src{path, text, D1.blank.inner(xx, ll, cc),
    tree, bound, items})) == 0n : Nat}

# LAW: blank reports no test under a name that is not `String.eq`
law blank_skips_aliased:
  for +path: String
  for e: {Paths.is_law_file(path) == False{} : Bool}
  for xx: String
  for +ll: U32
  for +cc: U32
  for text: String
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Blank.check(Src.Src{path, text, D1.blank.aliased(xx, ll, cc),
    tree, bound, items})) == 0n : Nat}

# LAW: blank reports no String.eq of `""` with what is not a plain name
law blank_skips_number:
  for +path: String
  for e: {Paths.is_law_file(path) == False{} : Bool}
  for xx: String
  for +ll: U32
  for +cc: U32
  for text: String
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Blank.check(Src.Src{path, text, D1.blank.number(xx, ll, cc),
    tree, bound, items})) == 0n : Nat}

# LAW: blank reports no String.eq whose `""` no comma comes before
law blank_skips_joined:
  for +path: String
  for e: {Paths.is_law_file(path) == False{} : Bool}
  for xx: String
  for +ll: U32
  for +cc: U32
  for text: String
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Blank.check(Src.Src{path, text, D1.blank.joined(xx, ll, cc),
    tree, bound, items})) == 0n : Nat}

# LAW: blank reports no String.eq whose second argument goes on past `""`
law blank_skips_longer:
  for +path: String
  for e: {Paths.is_law_file(path) == False{} : Bool}
  for +xx: String
  for +ll: U32
  for +cc: U32
  for text: String
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Blank.check(Src.Src{path, text, D1.blank.longer(xx, ll, cc),
    tree, bound, items})) == 0n : Nat}
