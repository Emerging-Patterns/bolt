# `hoist` reports exactly, in a def that calls itself and is not a law or a
# proof, outside a lambda's body (the rest of a chain after `=>`), a case
# pattern, and a case arm that does not call the def: a `List.get`,
# `List.set`, `String.get`, `Array.get` or `Array.set` call whose collection
# is a table, and a let of one plain name to a table that a later get, set or
# `name[..]` in its block or the statements after it indexes; where a table is
# a list literal with eight or more top-level commas, an array literal of more
# than eight slots (`[v : T*n]` with n not a literal 0 to 8, `[v : T^d]` with
# d not a literal 0 to 3), a `List.replicate`, `Array.new` or `List.range`
# whose count is not a literal 0 to 8, a `List.map` or `Array.map`, or a call
# to a def of the file, other than an undotted self-call, whose body is a
# single statement that is a list literal, or an array literal,
# `List.replicate`, `Array.new` or `List.range` sized by a number literal, of
# more than eight cells by those measures; and every value name in the table
# (a callee or a `~` template aside) is a parameter that each self-call passes
# back unchanged in its own position.
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/syntax/bind.bend as Bind
import ../src/src.bend as Src
import ../src/syntax/tree.bend as Tree
import ../src/syntax/outline.bend as Outline
import ../src/rules/suspicious/hoist.bend as Hoist
import ../src/rules/calls.bend as Calls
import ../src/rules/tokens.bend as T

# The recursion rule, hoist. It reads each def of the file whose body calls
# its own name and that is not a law or a proof, and walks that body as
# chains: a `=>` token makes the rest of its chain cold, a case's pattern is
# cold, and a case arm's body stays hot only when it calls the def; the rest
# keeps the heat it came in with, and the def's body starts hot. On a hot
# path it reports each call, a name token then a `(` group, that is a
# `List.get` / `List.set` (collection argument 2), `String.get` (0) or
# `Array.get` / `Array.set` (1) whose collection is a table, and each
# statement that is not a case, whose tokens before its first `=` hold exactly
# one lowercase name and no constructor or group, whose right side is a
# table, and whose name is indexed (`name[..]`, or a get or set's collection,
# bare or in parentheses) anywhere in its own block or the statements after
# it. A table is the rule's own recognizer (`is_table`): a list literal with
# eight or more top-level commas, an array literal `[v : T*n]` or `[v : T^d]`
# whose size is not a literal 0 to 8 after `*` or 0 to 3 after `^` (2^d
# slots), a `List.replicate` / `Array.new` / `List.range` whose count is not
# such a literal, a `List.map` / `Array.map`, or a call to a def of the file
# (not an undotted self-call) whose body is one constant-size table of that
# width (`wide_defs`); in every case
# with each value name under it (callees, `~` templates, dotted names and
# types aside) a parameter that every self-call passes back as that same lone
# name in its own position.

# does a get or set's collection argument, at its slot, hold a table?
def hoist.slot(
  ss: Hoist.Slot,
  +as: List<&2, Tree.Node>,
  +self: String,
  +wides: List<&2, String>,
  +carried: List<&2, String>
) -> Bool:
  match ss:
    case Hoist.Slot{on, at}:
      Bool.and(on, Hoist.is_table(Calls.arg(as, at), self, wides, carried))

# does a call site report: hot, a `(` group, and a get or set on a table
def hoist.call(
  +hot: Bool,
  +open: Bool,
  +tt: String,
  kids: Tree.Node,
  +self: String,
  +wides: List<&2, String>,
  +carried: List<&2, String>
) -> Bool:
  Bool.and(hot, Bool.and(open, hoist.slot(Hoist.slot_of(tt), Calls.args(kids), self, wides, carried)))

# a plain let's name and right side: a table, and the name indexed afterwards
def hoist.got(
  mm: Maybe<&2, Hoist.Got>,
  +body: Tree.Node,
  +rest: Tree.Node,
  +self: String,
  +wides: List<&2, String>,
  +carried: List<&2, String>
) -> Bool:
  match mm:
    case None{}:
      False{}
    case Some{Hoist.Got{+nm, +expr}}:
      Bool.and(Hoist.is_table(expr, self, wides, carried), Hoist.uses_or(body, rest, nm))

# does a statement report: hot, and a plain let of a table indexed afterwards
def hoist.let(
  +hot: Bool,
  kids: Tree.Node,
  +body: Tree.Node,
  +rest: Tree.Node,
  +self: String,
  +wides: List<&2, String>,
  +carried: List<&2, String>
) -> Bool:
  Bool.and(hot, hoist.got(Hoist.eat(kids, False{}, False{}, ""), body, rest, self, wides, carried))

# how many calls and lets hoist reports under the node, entered hot or cold
def hoist.count(
  nn: Tree.Node,
  +self: String,
  +wides: List<&2, String>,
  +carried: List<&2, String>,
  +hot: Bool
) -> Nat:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, +t, l, c}}, Tree.NCons{Tree.Group{Lex.Tok{_, +o, _, _}, +kids, _}, rest}}:
      +heat = Hoist.warm(hot, k)
      Nat.add(Bool.pick(Nat, hoist.call(heat, String.eq(o, "("), t, kids, self, wides, carried), 1n, 0n),
        Nat.add(hoist.count(kids, self, wides, carried, heat), hoist.count(rest, self, wides, carried, heat)))
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}}, rest}:
      hoist.count(rest, self, wides, carried, Hoist.warm(hot, k))
    case Tree.NCons{Tree.Group{o, kids, cl}, rest}:
      Nat.add(hoist.count(kids, self, wides, carried, hot), hoist.count(rest, self, wides, carried, hot))
    case Tree.NCons{Tree.Stmt{Tree.SCase{}, kids, +body}, rest}:
      Nat.add(hoist.count(kids, self, wides, carried, False{}),
        Nat.add(hoist.count(body, self, wides, carried, Bool.and(hot, Calls.calls(body, self))),
          hoist.count(rest, self, wides, carried, hot)))
    case Tree.NCons{Tree.Stmt{kind, +kids, +body}, +rest}:
      Nat.add(Bool.pick(Nat, hoist.let(hot, kids, body, rest, self, wides, carried), 1n, 0n),
        Nat.add(hoist.count(kids, self, wides, carried, hot),
          Nat.add(hoist.count(body, self, wides, carried, hot), hoist.count(rest, self, wides, carried, hot))))
    case Tree.NCons{h, rest}:
      hoist.count(rest, self, wides, carried, hot)
    case other:
      0n

# how many hoist reports over the defs: those in each def that calls itself
# and is not a law or a proof, walked hot, with its carried parameters
def hoist.total(ds: List<&2, Calls.Def>, +wides: List<&2, String>, +path: String) -> Nat:
  match ds:
    case Nil{}:
      0n
    case Con{Calls.Def{+name, +sig, +body}, rest}:
      Nat.add(Bool.pick(Nat, Bool.and(Calls.calls(body, name), Bool.not(Calls.exempt(path, sig))),
        hoist.count(body, name, wides, Hoist.carried(sig, body, name), True{}), 0n), hoist.total(rest, wides, path))

# LAW: hoist reports one finding for each call and each let the walk above
# counts, in each def that calls itself and is not a law or a proof, with
# the file's defs whose body is one wide constant-size table as builders;
# none for anything else
law hoist_counts:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for +tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Hoist.check(Src.Src{path, text, toks, tree, bound, items}))
    == hoist.total(Calls.defs(tree), Hoist.wide_defs(Calls.defs(tree), []), path) : Nat}
