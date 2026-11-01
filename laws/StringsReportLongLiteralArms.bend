# `strings` reports exactly a match whose closed string-literal arms, read in
# the first match column, total over 64 characters.
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/syntax/bind.bend as Bind
import ../src/src.bend as Src
import ../src/syntax/tree.bend as Tree
import ../src/syntax/outline.bend as Outline
import ../src/rules/perf/strings.bend as Strings
import ./defs/MatchArmRules.bend as D1

# the chars between the quotes of the string a case statement's first match
# column opens with, when it does and the string is closed, else zero
def strings.size(kids: Tree.Node) -> U32:
  match kids:
    case Tree.NCons{k, Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TStr{}, +t, l, c}}, rest}}:
      Bool.pick(U32, Strings.terminated(t), (U32.from_nat(String.length(t)) - 2 : U32), 0)
    case other:
      0

# acc and the chars of the closed string arms among a match body's statements
def strings.total(body: Tree.Node, +acc: U32) -> U32:
  match body:
    case Tree.NCons{Tree.Stmt{Tree.SCase{}, kids, b}, rest}:
      strings.total(rest, (acc + strings.size(kids) : U32))
    case Tree.NCons{h, rest}:
      strings.total(rest, acc)
    case other:
      acc

# how many statements, at any depth, are a match whose closed string arms
# total over 64 chars
def strings.count(nn: Tree.Node) -> Nat:
  match nn:
    case Tree.NCons{Tree.Stmt{kind, +kids, +body}, rest}:
      Nat.add(Bool.pick(Nat, Bool.and(D1.chars.is_match(kids), U32.is_gt(strings.total(body, 0), 64)), 1n, 0n),
        Nat.add(strings.count(body), strings.count(rest)))
    case Tree.NCons{h, rest}:
      strings.count(rest)
    case other:
      0n

# LAW: strings reports one finding for each match, at any depth, whose case
# arms opening their first match column with a closed string literal total
# over 64 chars between their quotes, and none for anything else: an
# unclosed string or one in a later column does not count
law strings_counts:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Strings.check(Src.Src{path, text, toks, tree, bound, items})) == strings.count(tree)
    : Nat}
