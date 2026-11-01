# `table` reports exactly, in a def that calls itself, a `List.get` or
# `List.set` call whose index is not one number token and whose list is a
# fixed table: a list literal, a number-sized array, or `List.replicate` /
# `Array.new` / `List.range` with a number count, written inline, as a table
# def of the file, or held by the let of that name in scope.
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/syntax/bind.bend as Bind
import ../src/src.bend as Src
import ../src/syntax/tree.bend as Tree
import ../src/syntax/outline.bend as Outline
import ../src/rules/suspicious/table.bend as Table
import ../src/rules/calls.bend as Calls
import ../src/rules/tokens.bend as T

# The table rules: table (laws/TableReportsFixedTableAccess.bend) and ring (laws/RingReportsDropAppendRotation.bend).
# Each
# reads each def of the file whose body calls it, `name(..)` (Calls.calls),
# and is not exempt, and walks that body at any depth: a call site is a name
# token then a group.

# table: is the call `List.get(..)` or `List.set(..)` whose index (argument
# 3, counting `&2` and the type) is not one number token (Table.literal) and
# whose list (argument 2) is a fixed table (Table.owns): a list literal with
# a top-level comma, a `[v : T*n]` or `[v : T^n]` array sized by a number, or
# `List.replicate` / `Array.new` / `List.range` with a number count, written
# inline, as `name()` or `name` for a def of the file whose body is one such
# table (Table.modules), or as a use of a name whose let in scope binds one
# (Table.scope). A let reaches the statements after it and their blocks, not
# an enclosing block or a sibling case arm, and a later let of the name to
# anything else ends it; a case pattern, a lambda or a parameter binding the
# same name does not end it.
def table.site(+tt: String, +op: String, kids: Tree.Node, +fixed: List<&2, String>) -> Bool:
  +as = Calls.args(kids)
  Bool.and(Bool.and(String.eq(op, "("), Bool.or(String.eq(tt, "List.get"), String.eq(tt, "List.set"))),
    Bool.and(Bool.not(Table.literal(Calls.arg(as, 3n))), Table.owns(Calls.arg(as, 2n), fixed)))

# how many call sites under the node, at any depth, are a fixed-table get or
# set at a computed index
def table.count(nn: Tree.Node, +fixed: List<&2, String>) -> Nat:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, +t, l, c}}, Tree.NCons{Tree.Group{Lex.Tok{_k, +o, _l, _c}, +kids, _e}, rest}}:
      Nat.add(Bool.pick(Nat, table.site(t, o, kids, fixed), 1n, 0n),
        Nat.add(table.count(kids, fixed), table.count(rest, fixed)))
    case Tree.NCons{Tree.Group{open, kids, close}, rest}:
      Nat.add(table.count(kids, fixed), table.count(rest, fixed))
    case Tree.NCons{Tree.Stmt{kind, kids, body}, rest}:
      Nat.add(table.count(kids, fixed), Nat.add(table.count(body, fixed), table.count(rest, fixed)))
    case Tree.NCons{h, rest}:
      table.count(rest, fixed)
    case other:
      0n

# LAW: over any chain, table reports one finding for each fixed-table
# `List.get(..)` or `List.set(..)` at an index that is not one number token,
# and none for any other call: a literal index (0 and 1 included), a list
# that is not a fixed table, `List.head` and `List.tail` stay quiet
law table_walk_counts:
  for nn: Tree.Node
  for +path: String
  for +fixed: List<&2, String>
  {List.length(&2, F.Finding, Table.walk(nn, path, fixed)) == table.count(nn, fixed) : Nat}

# the fixed-table gets and sets of each def of the list that calls itself
# and is not exempt, the tables in scope of its body
def table.defs(ds: List<&2, Calls.Def>, +mods: List<&2, String>, +path: String) -> Nat:
  match ds:
    case Nil{}:
      0n
    case Con{Calls.Def{+name, +sig, +body}, rest}:
      Nat.add(Bool.pick(Nat, Bool.and(Calls.calls(body, name), Bool.not(Calls.exempt(path, sig))),
        table.count(body, Table.scope(body, mods)), 0n), table.defs(rest, mods, path))

# LAW: table reports exactly those gets and sets, def by def, over the defs
# of the tree that call themselves, and none in a def that does not
law table_counts:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for +tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Table.check(Src.Src{path, text, toks, tree, bound, items}))
    == table.defs(Calls.defs(tree), Table.modules(Calls.defs(tree), []), path) : Nat}
