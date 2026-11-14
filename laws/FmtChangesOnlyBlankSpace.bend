# `bolt fmt` changes blank space and nothing else: the tokens of a file that
# are code (every token but spaces, newlines and comments), each by its kind
# and its text, are the same after formatting as before, in the same order.
# So a formatted file is the same program. This holds of each pass (the
# spaces inside a line, which are two steps, commas and runs; the def
# headers, from any state; trim; squeeze, from any run of newlines; close)
# and so of them all together.
#
# The header pass leaves alone what it has no business with: outside a
# header every token is written as it is, blank space too, and a `def`
# whose header needs no rewriting does not start one.
#
# Of the final newline three things are proved: a file that is one token of
# code gains it, unless the token's text ends in a line break; a file that
# is nothing but newlines, however many, closes to one; and a file whose
# last token is no newline, yet ends in a line break, is left as it ends.
# That last is a file that ends inside a string that never closes: the
# string runs through the file's last line break, so a newline after it
# would be one more on every run.
#
# Not proved here, and checked instead over the 10,158 files of 83 public
# repos and this repo's own: that a comment keeps its text but for the
# blanks it ends in, that the result has no blank before a line's end and no
# two blank lines in a row, that every file ends in one newline, and that
# formatting a formatted file changes nothing. That a rewritten header has
# the shape `wrap` asks for was checked over sixteen of those repos (its
# findings there fell from 8,920 to 215, none left in a header the pass
# rewrote).
import Base
import ../src/fmt.bend as Fmt
import ../src/fmt/head.bend as Head
import ../src/fmt/line.bend as Line
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

# LAW: putting a space after each comma keeps the code
law commas_keep_code:
  for toks: List<&2, Lex.Tok>
  {code(Line.commas(toks)) == code(toks) : List<&2, Lex.Tok>}

# LAW: making each run of spaces one keeps the code, whether the tokens
# start a line or not
law runs_keep_code:
  for toks: List<&2, Lex.Tok>
  for lead: Bool
  {code(Line.runs(toks, lead)) == code(toks) : List<&2, Lex.Tok>}

# LAW: the def-header pass keeps the code, whether it starts outside a
# header or inside one it is rewriting
law heads_keep_code:
  for toks: List<&2, Lex.Tok>
  for +st: Head.State
  {code(Head.heads.go(toks, st)) == code(toks) : List<&2, Lex.Tok>}

# LAW: outside a header, a token that is no `def` at column 0 is written as
# it is, blank space included, and the pass stays outside
law heads_pass_other_tokens:
  for k: Lex.TokKind
  for +t: String
  for +l: U32
  for +c: U32
  for +rest: List<&2, Lex.Tok>
  for e: {Head.starts(Lex.Tok{k, t, l, c}) == False{} : Bool}
  {Head.heads.go(Lex.Tok{k, t, l, c} <> rest, Head.Out{}) == Lex.Tok{k, t, l, c} <> Head.heads.go(rest, Head.Out{})
    : List<&2, Lex.Tok>}

# LAW: a `def` whose header needs no rewriting (it fits on its one line, or
# never reaches a `:`) is written as it is, and the pass stays outside, so
# that header's blank space is left alone
law heads_leave_fitting_header:
  for +t: String
  for +l: U32
  for +c: U32
  for +rest: List<&2, Lex.Tok>
  for e: {Head.needs(rest, 0, 3, False{}) == False{} : Bool}
  {Head.heads.go(Lex.Tok{Lex.TKey{}, t, l, c} <> rest, Head.Out{})
    == Lex.Tok{Lex.TKey{}, t, l, c} <> Head.heads.go(rest, Head.Out{}) : List<&2, Lex.Tok>}

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

# one newline more than the count
def newlines(kn: Nat) -> List<&2, Lex.Tok>:
  match kn:
    case 0n:
      [Lex.Tok{Lex.TNewline{}, "\n", 0, 0}]
    case 1n+p:
      Lex.Tok{Lex.TNewline{}, "\n", 0, 0} <> newlines(p)

# LAW: a file of one token that is no newline, and whose text ends in no
# line break, is closed with a newline after it
law close_adds_final_newline:
  for +k: Lex.TokKind
  for +t: String
  for l: U32
  for c: U32
  for e: {Fmt.is_newline(k) == False{} : Bool}
  for b: {Fmt.close.broken(t) == False{} : Bool}
  {Fmt.close([Lex.Tok{k, t, l, c}]) == [Lex.Tok{k, t, l, c}, Fmt.close.newline()] : List<&2, Lex.Tok>}

# LAW: tokens that end in one that is no newline, yet whose text ends in a
# line break, are left as they are: a file that ends inside a string
law close_leaves_unclosed_string:
  for +toks: List<&2, Lex.Tok>
  for e: {Fmt.close.shut(toks) == True{} : Bool}
  {Fmt.close(toks) == toks : List<&2, Lex.Tok>}

# LAW: newlines alone, however many, close to one
law close_newlines_to_one:
  for kn: Nat
  {Fmt.close.go(newlines(kn)) == [Fmt.close.newline()] : List<&2, Lex.Tok>}

# LAW: formatting keeps the code: the same tokens of code, kind and text, in
# the same order
law fmt_keeps_code:
  for +toks: List<&2, Lex.Tok>
  {code(Fmt.toks(toks)) == code(toks) : List<&2, Lex.Tok>}
