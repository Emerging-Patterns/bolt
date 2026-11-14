# `bolt fmt` changes blank space and nothing else: the tokens of a file that
# are code (every token but spaces, newlines and comments), each by its kind
# and its text, are the same after formatting as before, in the same order.
# So a formatted file is the same program. This holds of each pass (trim,
# squeeze from any run of newlines, close) and so of the three together.
#
# Not proved here, and checked instead over 2,012 files (this repo's and
# 1,500 public ones): that a comment keeps its text but for the blanks it
# ends in, that the result has no blank before a line's end, no two blank
# lines in a row and one final newline, and that formatting a formatted file
# changes nothing.
import Base
import ../src/fmt.bend as Fmt
import ../src/syntax/lex.bend as Lex

# the tokens that are code, each by its kind and text, in order: where a
# token sits is not part of it
def code(toks: List<&2, Lex.Tok>) -> List<&2, Lex.Tok>:
  match toks:
    case Nil{}:
      Nil{}
    case Con{Lex.Tok{+k, t, _l, _c}, rest}:
      +more = code(rest)
      Bool.pick(List<&2, Lex.Tok>, Lex.significant(k), Lex.Tok{k, t, 0, 0} <> more, more)

# LAW: trim keeps the code
law trim_keeps_code:
  for toks: List<&2, Lex.Tok>
  {code(Fmt.trim(toks)) == code(toks) : List<&2, Lex.Tok>}

# LAW: squeeze keeps the code, whatever run of newlines came before
law squeeze_keeps_code:
  for toks: List<&2, Lex.Tok>
  for +run: U32
  {code(Fmt.squeeze(toks, run)) == code(toks) : List<&2, Lex.Tok>}

# LAW: close keeps the code
law close_keeps_code:
  for toks: List<&2, Lex.Tok>
  {code(Fmt.close(toks)) == code(toks) : List<&2, Lex.Tok>}

# LAW: formatting keeps the code: the same tokens of code, kind and text, in
# the same order
law fmt_keeps_code:
  for +toks: List<&2, Lex.Tok>
  {code(Fmt.toks(toks)) == code(toks) : List<&2, Lex.Tok>}
