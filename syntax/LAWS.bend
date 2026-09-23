# syntax: the laws. Each quantifies over every source, never one fixture.
import Base
import ./lex.bend as Lex
import ./tree.bend as Tree
import ../lazy/lazy.bend as Lazy

# LAW: the tokens' texts spell the source back, whatever the source is
# BOLT-SYN-1
law lossless:
  for +s: String
  {Lex.text(Lex.tokens(s)) == s : String}

# is the char a line break? '\n', code point 10
def breaks(cc: Char) -> Bool:
  U32.is_eq(Char.to_u32(cc), 10)

# the line reading a text ends on, from line ln: one more per line break
def line_after(src: String, +ln: U32) -> U32:
  match src:
    case SNil{}:
      ln
    case SCon{h, t}:
      line_after(t, Bool.pick(U32, breaks(h), (ln + 1 : U32), ln))

# the column reading a text ends on, from column cn: one more per code point,
# back to 0 after a line break
def col_after(src: String, +cn: U32) -> U32:
  match src:
    case SNil{}:
      cn
    case SCon{h, t}:
      col_after(t, Bool.pick(U32, breaks(h), 0, (cn + 1 : U32)))

# the tokens, each moved to where reading the texts before it from (ln, cn)
# ends: the position of its first char
def placed(toks: List<&2, Lex.Tok>, +ln: U32, +cn: U32) -> List<&2, Lex.Tok>:
  match toks:
    case Nil{}:
      []
    case Con{Lex.Tok{k, +t, _l, _c}, rest}:
      Lex.Tok{k, t, ln, cn} <> placed(rest, line_after(t, ln), col_after(t, cn))

# LAW: every token already sits where placed puts it. By lossless, the texts
# before a token are the source up to its first char, so its line and column
# are that char's, 0-based, counting code points
# BOLT-SYN-2
law positions:
  for +s: String
  {placed(Lex.tokens(s), 0, 0) == Lex.tokens(s) : List<&2, Lex.Tok>}

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
# BOLT-SYN-3
law leaves:
  for +toks: List<&2, Lex.Tok>
  {Tree.leaves(Tree.of_tokens(toks)) == split_gts(significant(toks)) : List<&2, Lex.Tok>}
