# The tree drops no token: its leaves are the significant tokens in order,
# except that each token that is a run of `>` (a close of angle groups or an
# operator such as `>>`) becomes one `>` leaf per character at consecutive
# columns.
import Base
import ../src/syntax/lex.bend as Lex
import ../src/syntax/tree.bend as Tree
import ../src/lazy/lazy.bend as Lazy

# the significant tokens, in order: no space, newline or comment
def significant(toks: List<&2, Lex.Tok>) -> List<&2, Lex.Tok>:
  match toks:
    case Nil{}:
      []
    case Con{Lex.Tok{+k, t, l, c}, rest}:
      +more = significant(rest)
      Bool.pick(List<&2, Lex.Tok>, Lex.significant(k), Lex.Tok{k, t, l, c} <> more, more)

# is every char a `>`?
def only_gt(cs: List<&2, Char>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{+ch, t}:
      Lazy.and_then(Char.is_eq(ch, '>'), _u => only_gt(t))

# a token the tree reads as a run of closing `>`: an operator of one or more
# `>` and nothing else (`>`, `>>`), whatever is open when it comes; also a
# close bracket whose text starts with `>`, which the lexer never makes (its
# close brackets are `)`, `]` and `}`)
def gt_run(kk: Lex.TokKind, +tt: String) -> Bool:
  match kk:
    case Lex.TOp{}:
      Bool.and(Bool.not(String.is_empty(tt)), only_gt(String.to_list(tt)))
    case Lex.TClose{}:
      String.starts_with(tt, ">")
    case other:
      False{}

# one `>` operator per char, on line ln at consecutive columns from cn
def gts(cs: List<&2, Char>, +ln: U32, +cn: U32) -> List<&2, Lex.Tok>:
  match cs:
    case Nil{}:
      []
    case Con{_ch, t}:
      Lex.Tok{Lex.TOp{}, ">", ln, cn} <> gts(t, ln, (cn + 1 : U32))

# the tokens in order, each run of `>` split into one `>` per char
def split_gts(toks: List<&2, Lex.Tok>) -> List<&2, Lex.Tok>:
  match toks:
    case Nil{}:
      []
    case Con{Lex.Tok{+k, +t, +l, +c}, rest}:
      List.append(&2, Lex.Tok,
        Bool.pick(List<&2, Lex.Tok>, gt_run(k, t), gts(String.to_list(t), l, c), [Lex.Tok{k, t, l, c}]),
        split_gts(rest))

# LAW: the tree drops no token and adds none: read back in order, its leaves
# are the significant tokens, except that a run of `>` becomes one `>` leaf
# per char, at consecutive columns (each closes the angle group on top, or is
# a stray leaf when there is none: an operator `>>` is split too)
law leaves:
  for +toks: List<&2, Lex.Tok>
  {Tree.leaves(Tree.of_tokens(toks)) == split_gts(significant(toks)) : List<&2, Lex.Tok>}
