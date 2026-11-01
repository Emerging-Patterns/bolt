# `fromrev` reports exactly, outside a LAWS.bend or a PROOF.bend, one finding
# (on the first) for each run of four tokens right after one another among the
# significant tokens (spaces, newlines and comments dropped) whose texts are
# `String.from_list`, `(`, `List.reverse` and `(`, and nothing else: anything
# between them, another `(` included, is not the shape, and neither is
# `List.reverse.go`.
#
# also rests on: laws/FromrevExempt.bend, laws/InertFromrev.bend
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/syntax/bind.bend as Bind
import ../src/paths.bend as Paths
import ../src/src.bend as Src
import ../src/syntax/tree.bend as Tree
import ../src/syntax/outline.bend as Outline
import ../src/rules/suspicious/fromrev.bend as Fromrev
import ../src/rules/tokens.bend as T

# True when tt is `String.from_list` and the tokens open with `(`,
# `List.reverse` and `(`
def fromrev_at(+tt: String, toks: List<&2, Lex.Tok>) -> Bool:
  match toks:
    case Nil{}:
      False{}
    case Con{Lex.Tok{k1, +a, l1, c1}, r1}:
      match r1:
        case Nil{}:
          False{}
        case Con{Lex.Tok{k2, +b, l2, c2}, r2}:
          match r2:
            case Nil{}:
              False{}
            case Con{Lex.Tok{k3, +d, l3, c3}, r3}:
              Bool.and(Bool.and(String.eq(tt, "String.from_list"), String.eq(a, "(")),
                Bool.and(String.eq(b, "List.reverse"), String.eq(d, "(")))

# how many tokens start a `String.from_list`, `(`, `List.reverse`, `(` run
def fromrev_count(toks: List<&2, Lex.Tok>) -> Nat:
  match toks:
    case Nil{}:
      0n
    case Con{Lex.Tok{k, +t, l, c}, +rest}:
      +m = fromrev_count(rest)
      Bool.pick(Nat, fromrev_at(t, rest), 1n+m, m)

# LAW: fromrev reports, outside a LAWS.bend or a PROOF.bend, one finding for
# each run of significant tokens whose texts are `String.from_list`, `(`,
# `List.reverse` and `(`, and none for any other token
law fromrev_counts:
  for +path: String
  for text: String
  for +toks: List<&2, Lex.Tok>
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Fromrev.check(Src.Src{path, text, toks, tree, bound, items}))
    == Bool.pick(Nat, Paths.is_law_file(path), 0n, fromrev_count(T.sig(toks))) : Nat}
