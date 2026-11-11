# `chars` reports exactly a match with more than eight arms whose first match
# column opens with a char literal.
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/syntax/bind.bend as Bind
import ../src/src.bend as Src
import ../src/syntax/tree.bend as Tree
import ../src/syntax/outline.bend as Outline
import ../src/rules/pedantic/chars.bend as Chars
import ./defs/MatchArmRules.bend as D1

# one when a case statement's first match column opens with a char literal,
# else zero
def chars.opens(kids: Tree.Node) -> U32:
  match kids:
    case Tree.NCons{k, Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TChar{}, t, l, c}}, rest}}:
      1
    case other:
      0

# acc and the case statements among a match body's statements that open
# with a char literal
def chars.arms(body: Tree.Node, +acc: U32) -> U32:
  match body:
    case Tree.NCons{Tree.Stmt{Tree.SCase{}, kids, b}, rest}:
      chars.arms(rest, (acc + chars.opens(kids) : U32))
    case Tree.NCons{h, rest}:
      chars.arms(rest, acc)
    case other:
      acc

# how many statements, at any depth, are a match with more than eight arms
# opening with a char literal
def chars.count(nn: Tree.Node) -> Nat:
  match nn:
    case Tree.NCons{Tree.Stmt{kind, +kids, +body}, rest}:
      Nat.add(Bool.pick(Nat, Bool.and(D1.chars.is_match(kids), U32.is_gt(chars.arms(body, 0), 8)), 1n, 0n),
        Nat.add(chars.count(body), chars.count(rest)))
    case Tree.NCons{h, rest}:
      chars.count(rest)
    case other:
      0n

# LAW: chars reports one finding for each match, at any depth, with more than
# eight case arms whose first match column opens with a char literal, and
# none for anything else: a literal later in a pattern or in a later column
# does not count
law chars_counts:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Chars.check(Src.Src{path, text, toks, tree, bound, items})) == chars.count(tree)
    : Nat}
