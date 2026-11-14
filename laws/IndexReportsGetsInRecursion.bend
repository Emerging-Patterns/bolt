# `index` reports exactly a `List.get` or `String.get` at a non-literal index
# anywhere in a recursive def, except a `List.get` on a fixed table
# (src/rules/table.bend) and a get that is the def's own self-call (the def is named
# `List.get` or `String.get`).
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/syntax/bind.bend as Bind
import ../src/src.bend as Src
import ../src/syntax/tree.bend as Tree
import ../src/syntax/outline.bend as Outline
import ../src/rules/pedantic/index.bend as Index
import ../src/rules/table.bend as Table
import ../src/rules/calls.bend as Calls

# The recursion rule, index. It reads each def of the file whose body calls
# its own name and that is not a law or a proof, and every call in that body
# at any depth: a name token, then a group. A `String.get(..)` whose index
# (argument 1) is not one number token is a finding. So is a `List.get(..)`
# whose index (argument 3) is not one number token, unless src/rules/table.bend
# calls it a get on a fixed table, over the tables it finds in that def.
# A call whose name is the def's own (a def named `List.get` or `String.get`
# stepping to itself) is neither.

# is the chain exactly one number token?
def index.lit(n: Tree.Node) -> Bool:
  match n:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TNum{}, t, l, c}}, Tree.NNil{}}:
      True{}
    case other:
      False{}

# does a call report, given whether its name is List.get (list) or
# String.get (sget), whether its group opens with `(` (ob), its arguments,
# and what src/rules/table.bend makes of it (a finding when it is a fixed
# table's)?
def index.fires(list: Bool, +ob: Bool, +sget: Bool, +as: List<&2, Tree.Node>, table: List<&2, F.Finding>) -> Bool:
  match list:
    case True{}:
      Bool.and(ob, Bool.and(Bool.not(index.lit(Calls.arg(as, 3n))), List.is_empty(&2, F.Finding, table)))
    case False{}:
      Bool.and(ob, Bool.and(sget, Bool.not(index.lit(Calls.arg(as, 1n)))))

# one when the name token t at (l, c), then the rest, is a call index
# reports in the def named self
def index.site(
  +t: String,
  +l: U32,
  +c: U32,
  rest: Tree.Node,
  +path: String,
  +fixed: List<&2, String>,
  +self: String
) -> Nat:
  match rest:
    case Tree.NCons{Tree.Group{Lex.Tok{k, +o, ol, oc}, +kids, cl}, r}:
      +other = Bool.not(String.eq(t, self))
      Bool.pick(Nat, index.fires(Bool.and(String.eq(t, "List.get"), other), String.eq(o, "("),
        Bool.and(String.eq(t, "String.get"), other),
        Calls.args(kids), Table.hit(String.eq(o, "("), "List.get", kids, fixed, path, l, c)), 1n, 0n)
    case other:
      0n

# how many calls at any depth of the node index reports, fixed the tables
# src/rules/table.bend sees, in the def named self
def index.count(nn: Tree.Node, +path: String, +fixed: List<&2, String>, +self: String) -> Nat:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, +t, +l, +c}}, +rest}:
      Nat.add(index.site(t, l, c, rest, path, fixed, self), index.count(rest, path, fixed, self))
    case Tree.NCons{Tree.Group{o, kids, cl}, rest}:
      Nat.add(index.count(kids, path, fixed, self), index.count(rest, path, fixed, self))
    case Tree.NCons{Tree.Stmt{kind, kids, body}, rest}:
      Nat.add(index.count(kids, path, fixed, self), Nat.add(index.count(body, path, fixed, self),
        index.count(rest, path, fixed, self)))
    case Tree.NCons{h, rest}:
      index.count(rest, path, fixed, self)
    case other:
      0n

# how many calls index reports over the defs: those in each def that calls
# itself and is not a law or a proof, with the fixed tables it holds
def index.total(ds: List<&2, Calls.Def>, +mods: List<&2, String>, +path: String) -> Nat:
  match ds:
    case Nil{}:
      0n
    case Con{Calls.Def{+name, +sig, +body}, rest}:
      Nat.add(Bool.pick(Nat, Bool.and(Calls.calls(body, name), Bool.not(Calls.exempt(path, sig))),
        index.count(body, path, Table.scope(body, mods), name), 0n), index.total(rest, mods, path))

# LAW: index reports one finding for each `List.get(..)` or `String.get(..)`
# at an index that is not one number token, anywhere in a def that calls
# itself (a base arm included) and is not a law or a proof, except a
# `List.get` on a fixed table (src/rules/table.bend) and a get that is
# the def's own self-call (in a def named `List.get` or `String.get`); none
# for anything else
law index_counts:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for +tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Index.check(Src.Src{path, text, toks, tree, bound, items}))
    == index.total(Calls.defs(tree), Table.modules(Calls.defs(tree), []), path) : Nat}
