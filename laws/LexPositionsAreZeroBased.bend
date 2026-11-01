# A token's line and column are those of its first character, 0-based, in code
# points.
import Base
import ../src/syntax/lex.bend as Lex
import ./defs/LineBreakChar.bend as D1

# the line reading a text ends on, from line ln: one more per line break
def line_after(src: String, +ln: U32) -> U32:
  match src:
    case SNil{}:
      ln
    case SCon{h, t}:
      line_after(t, Bool.pick(U32, D1.breaks(h), (ln + 1 : U32), ln))

# the column reading a text ends on, from column cn: one more per code point,
# back to 0 after a line break
def col_after(src: String, +cn: U32) -> U32:
  match src:
    case SNil{}:
      cn
    case SCon{h, t}:
      col_after(t, Bool.pick(U32, D1.breaks(h), 0, (cn + 1 : U32)))

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
law positions:
  for +s: String
  {placed(Lex.tokens(s), 0, 0) == Lex.tokens(s) : List<&2, Lex.Tok>}
