# src/fmt/line: the pass of bolt's formatter for the spaces inside a line.
# Two steps over a file's tokens:
#   commas  a comma has a space after it: one is put after a comma the next
#           token touches, unless that token is a closing bracket (`[a, b,]`
#           stays);
#   runs    one space between two tokens of a line: a run of spaces or tabs
#           that neither opens its line nor comes before a comment becomes
#           one space.
# A line's indentation is kept as written, and so are the spaces before a
# comment, which may be lined up with the comments around it. A space is
# put nowhere but after a comma, and none is taken away: `f(x)` and `f (x)`
# both stay, and so does `1n+p`.
# Pure.
import Base
import ../syntax/lex.bend as Lex

# may a comma not touch a token of this kind: any but blank space and a
# closing bracket?
def commas.far(k: Lex.TokKind) -> Bool:
  match k:
    case Lex.TSpace{}:
      False{}
    case Lex.TNewline{}:
      False{}
    case Lex.TClose{}:
      False{}
    case other:
      True{}

# does a comma right before these tokens want a space: there is a next
# token, and a comma may not touch it?
def commas.bare(rest: List<&2, Lex.Tok>) -> Bool:
  match rest:
    case Nil{}:
      False{}
    case Con{Lex.Tok{k, _t, _l, _c}, _more}:
      commas.far(k)

# one space
def space() -> Lex.Tok:
  Lex.Tok{Lex.TSpace{}, " ", 0, 0}

# the tokens after a comma, a space put first where the comma wants one
def commas.gap(bare: Bool, more: List<&2, Lex.Tok>) -> List<&2, Lex.Tok>:
  match bare:
    case True{}:
      space() <> more
    case False{}:
      more

# a space after every comma
def commas(toks: List<&2, Lex.Tok>) -> List<&2, Lex.Tok>:
  match toks:
    case Nil{}:
      Nil{}
    case Con{Lex.Tok{Lex.TComma{}, t, l, c}, +rest}:
      Lex.Tok{Lex.TComma{}, t, l, c} <> commas.gap(commas.bare(rest), commas(rest))
    case Con{tok, rest}:
      tok <> commas(rest)

# is the kind a comment's?
def runs.note(k: Lex.TokKind) -> Bool:
  match k:
    case Lex.TComment{}:
      True{}
    case other:
      False{}

# is the first of these tokens a comment?
def runs.noted(rest: List<&2, Lex.Tok>) -> Bool:
  match rest:
    case Nil{}:
      False{}
    case Con{Lex.Tok{k, _t, _l, _c}, _more}:
      runs.note(k)

# a space token's text: as written where it is kept, one space where not
def runs.text(keep: Bool, t: String) -> String:
  match keep:
    case True{}:
      t
    case False{}:
      " "

# one space between two tokens of a line. lead: does the next token open
# its line?
def runs(toks: List<&2, Lex.Tok>, lead: Bool) -> List<&2, Lex.Tok>:
  match toks:
    case Nil{}:
      Nil{}
    case Con{Lex.Tok{Lex.TSpace{}, t, l, c}, +rest}:
      Lex.Tok{Lex.TSpace{}, runs.text(Bool.or(lead, runs.noted(rest)), t), l, c} <> runs(rest, False{})
    case Con{Lex.Tok{Lex.TNewline{}, t, l, c}, rest}:
      Lex.Tok{Lex.TNewline{}, t, l, c} <> runs(rest, True{})
    case Con{tok, rest}:
      tok <> runs(rest, False{})

# a file's tokens with the spaces inside each line written one way
def spaces(toks: List<&2, Lex.Tok>) -> List<&2, Lex.Tok>:
  runs(commas(toks), True{})
