# `strict` reports exactly a self-call inside `Bool.and` or `Bool.or`, or in a
# comma-separated stretch holding `&&` or `||` (matched by that exact text),
# where a `=>` ends the stretch on its left and a lambda body counts only by
# its own `&&` or `||`.
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/syntax/bind.bend as Bind
import ../src/src.bend as Src
import ../src/syntax/tree.bend as Tree
import ../src/syntax/outline.bend as Outline
import ../src/rules/pedantic/strict.bend as Strict
import ../src/rules/calls.bend as Calls

# does the chain, up to its first top-level comma or `=>`, hold a `&&` or
# `||` operator (a stretch that is an operand of one)? A `=>` ends the
# stretch on its left, so a lambda body's operators never reach back past it
def strict.ops(n: Tree.Node) -> Bool:
  match n:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TComma{}, t, l, c}}, rest}:
      False{}
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TLam{}, t, l, c}}, rest}:
      False{}
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TOp{}, +t, l, c}}, rest}:
      Bool.or(Bool.or(String.eq(t, "&&"), String.eq(t, "||")), strict.ops(rest))
    case Tree.NCons{h, rest}:
      strict.ops(rest)
    case other:
      False{}

# how many self-calls in the chain, at any depth, sit in an eager operand:
# inside the `(..)` of `Bool.and` or `Bool.or`, or in a stretch (ended by a
# comma or a `=>`) holding `&&` or `||`. outer: the enclosing group is an
# operand; hot: the current stretch is. A `=>` starts a lambda body, an
# operand only by its own `&&` or `||`; a statement's own tokens start cold,
# its body colder.
def strict.count(nn: Tree.Node, +name: String, +outer: Bool, +hot: Bool) -> Nat:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TComma{}, t, l, c}}, +rest}:
      strict.count(rest, name, outer, Bool.or(outer, strict.ops(rest)))
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TLam{}, t, l, c}}, +rest}:
      strict.count(rest, name, outer, strict.ops(rest))
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, +t, l, c}}, Tree.NCons{Tree.Group{Lex.Tok{_, +o, _, _}, +kids, _}, rest}}:
      +call = String.eq(o, "(")
      +inner = Bool.or(hot, Bool.and(call, Bool.or(String.eq(t, "Bool.and"), String.eq(t, "Bool.or"))))
      +m = Nat.add(strict.count(kids, name, inner, Bool.or(inner, strict.ops(kids))),
        strict.count(rest, name, outer, hot))
      Bool.pick(Nat, Bool.and(Bool.and(call, String.eq(t, name)), hot), 1n+m, m)
    case Tree.NCons{Tree.Group{open, +kids, close}, rest}:
      Nat.add(strict.count(kids, name, hot, Bool.or(hot, strict.ops(kids))), strict.count(rest, name, outer, hot))
    case Tree.NCons{Tree.Stmt{kind, +kids, body}, rest}:
      Nat.add(strict.count(kids, name, False{}, strict.ops(kids)),
        Nat.add(strict.count(body, name, False{}, False{}), strict.count(rest, name, outer, hot)))
    case Tree.NCons{h, rest}:
      strict.count(rest, name, outer, hot)
    case other:
      0n

# LAW: over any chain, strict reports one finding for each self-call in an
# eager operand, matched by its exact text, and none for any other call
law strict_walk_counts:
  for n: Tree.Node
  for +name: String
  for +path: String
  for +outer: Bool
  for +hot: Bool
  {List.length(&2, F.Finding, Strict.walk(n, name, path, outer, hot)) == strict.count(n, name, outer, hot) : Nat}

# the self-calls in operands of each def of the list, none in an exempt one
def strict.defs(ds: List<&2, Calls.Def>, +path: String) -> Nat:
  match ds:
    case Nil{}:
      0n
    case Con{Calls.Def{+name, +sig, body}, rest}:
      Nat.add(Bool.pick(Nat, Calls.exempt(path, sig), 0n, strict.count(body, name, False{}, False{})),
        strict.defs(rest, path))

# LAW: strict reports exactly those self-calls, def by def, over the defs of
# the tree, each body starting cold
law strict_counts:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Strict.check(Src.Src{path, text, toks, tree, bound, items}))
    == strict.defs(Calls.defs(tree), path) : Nat}
