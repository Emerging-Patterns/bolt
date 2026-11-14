# src/fmt: bolt's formatter (`bolt fmt`). It changes blank space and nothing
# else: every token that is code is kept as it is, in order, and so is each
# comment but for the blanks it ends in. Four passes over a file's tokens:
#   heads    a def header that breaks across lines, or is too wide, takes
#            the shape `wrap` asks for (src/fmt/head.bend);
#   trim     no blank before a line's end: a space token right before a
#            newline, or before the end of the file, is dropped, and a
#            comment loses the spaces and tabs it ends in;
#   squeeze  no two blank lines in a row, and none at the top: once two
#            newlines have run, further ones are dropped, and the file opens
#            as if two already had;
#   close    one newline at the end: the newlines the tokens end in become
#            one, and a file that ends without one gains it. An empty file
#            stays empty.
# Indentation, the spaces inside a line, and where a line that is no def
# header breaks are left as they are.
# Pure: text in, text out. src/fmt/plan.bend decides which files change and
# src/fmt/run.bend writes them.
import Base
import ./lazy/lazy.bend as Lazy
import ./rchars.bend as Rchars
import ./syntax/lex.bend as Lex
import ./fmt/head.bend as Head

# a newline token?
def is_newline(k: Lex.TokKind) -> Bool:
  match k:
    case Lex.TNewline{}:
      True{}
    case other:
      False{}

# a space token: a run of spaces and tabs?
def is_space(k: Lex.TokKind) -> Bool:
  match k:
    case Lex.TSpace{}:
      True{}
    case other:
      False{}

# a space or a tab?
def blank(+ch: Char) -> Bool:
  Bool.or(Char.is_eq(ch, ' '), Char.is_eq(ch, '\t'))

# the chars after the blanks they open with
def trim.lead(cs: List<&2, Char>) -> List<&2, Char>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{+c, +t}:
      Lazy.either(List<&2, Char>, blank(c), _u => trim.lead(t), _v => c <> t)

# a text without the spaces and tabs it ends in
def trim.tail(t: String) -> String:
  Rchars.text(trim.lead(List.reverse(&2, Char, String.to_list(t))))

# a token's text as trim leaves it: a comment's without the blanks it ends
# in, any other as it is
def trim.text(k: Lex.TokKind, +t: String) -> String:
  match k:
    case Lex.TComment{}:
      trim.tail(t)
    case other:
      t

# does a line end here: at a newline, or at the end of the tokens?
def trim.ends(toks: List<&2, Lex.Tok>) -> Bool:
  match toks:
    case Nil{}:
      True{}
    case Con{Lex.Tok{k, _t, _l, _c}, _rest}:
      is_newline(k)

# a token kept, with its text trimmed, before the rest; or dropped
def trim.keep(drop: Bool, +k: Lex.TokKind, t: String, l: U32, c: U32, more: List<&2, Lex.Tok>) -> List<&2, Lex.Tok>:
  match drop:
    case True{}:
      more
    case False{}:
      Lex.Tok{k, trim.text(k, t), l, c} <> more

# no blank before a line's end
def trim(toks: List<&2, Lex.Tok>) -> List<&2, Lex.Tok>:
  match toks:
    case Nil{}:
      Nil{}
    case Con{Lex.Tok{+k, t, l, c}, +rest}:
      trim.keep(Lazy.and_then(is_space(k), _u => trim.ends(rest)), k, t, l, c, trim(rest))

# how many newlines in a row are kept: two, which is one blank line
def squeeze.most() -> U32:
  2

# the run of newlines after a token: one longer after a newline, none after
# anything else
def squeeze.run(nl: Bool, run: U32) -> U32:
  match nl:
    case True{}:
      (run + 1 : U32)
    case False{}:
      0

# no two blank lines in a row. run: how many newlines the tokens so far end
# in
def squeeze(toks: List<&2, Lex.Tok>, +run: U32) -> List<&2, Lex.Tok>:
  match toks:
    case Nil{}:
      Nil{}
    case Con{Lex.Tok{+k, t, l, c}, rest}:
      +nl = is_newline(k)
      +drop = Bool.and(nl, U32.is_ge(run, squeeze.most()))
      +more = squeeze(rest, Bool.pick(U32, drop, run, squeeze.run(nl, run)))
      Bool.pick(List<&2, Lex.Tok>, drop, more, Lex.Tok{k, t, l, c} <> more)

# are these all newlines?
def close.only(toks: List<&2, Lex.Tok>) -> Bool:
  match toks:
    case Nil{}:
      True{}
    case Con{Lex.Tok{k, _t, _l, _c}, rest}:
      Lazy.and_then(is_newline(k), _u => close.only(rest))

# the newline a file ends in
def close.newline() -> Lex.Tok:
  Lex.Tok{Lex.TNewline{}, "\n", 0, 0}

# the tokens through their last one that is no newline, then one newline
def close.go(toks: List<&2, Lex.Tok>) -> List<&2, Lex.Tok>:
  match toks:
    case Nil{}:
      [close.newline()]
    case Con{Lex.Tok{+k, t, l, c}, +rest}:
      Lazy.stop(List<&2, Lex.Tok>, Lazy.and_then(is_newline(k), _u => close.only(rest)), [close.newline()],
        _v => Lex.Tok{k, t, l, c} <> close.go(rest))

# one newline at the end; an empty file stays empty
def close(toks: List<&2, Lex.Tok>) -> List<&2, Lex.Tok>:
  match toks:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      close.go(h <> t)

# a file's tokens, formatted. The line and column of a token after the first
# change are the ones it was read at, not where it now sits: only the texts
# are read again
def toks(ts: List<&2, Lex.Tok>) -> List<&2, Lex.Tok>:
  close(squeeze(trim(Head.heads(ts)), squeeze.most()))

# a file's text, formatted
def text(source: String) -> String:
  Lex.text(toks(Lex.tokens(source)))
