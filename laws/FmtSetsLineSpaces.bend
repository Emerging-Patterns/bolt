# `bolt fmt` writes the spaces inside a line one way, in two steps over a
# file's tokens (src/fmt/line.bend).
#
# commas: after it every comma is followed by a space, a newline or a
# closing bracket, or is the last token. Tokens that already read so come
# back as they are, so the step done twice is the step done once. It adds
# space tokens and nothing else: every token that is no space is kept as it
# is, where it was, a comment and a newline included.
#
# runs: after it every space token that neither opens its line nor comes
# before a comment is one space. The step done twice is the step done once.
# It changes the text of space tokens and nothing else: with those texts
# set aside, the tokens are the ones that went in. A space that opens its
# line, which is the line's indentation, is kept as written, and so is a
# space before a comment.
#
# Both keep the code: laws/FmtChangesOnlyBlankSpace.bend.
#
# Not proved here: that the passes after these two leave the spaces so (the
# def-header pass writes the gaps of a header it rewrites), and that Bend
# reads a line the same before and after. Both were checked instead. Over
# the 10,158 files of 83 public repos the two steps changed 17,350 lines in
# 745 files and no token of code, and a second run changed nothing. This
# repo's own tree, with the space after each of 108,590 commas taken out
# and 34,743 spaces made three, came back byte for byte; and `bend` checked
# and built that respaced tree as it does the tree as written, into a bolt
# that reports the same findings.
import Base
import ../src/fmt/line.bend as Line
import ../src/syntax/lex.bend as Lex

# may a comma come right before a token of this kind: a space, a newline or
# a closing bracket?
def beside(k: Lex.TokKind) -> Bool:
  match k:
    case Lex.TSpace{}:
      True{}
    case Lex.TNewline{}:
      True{}
    case Lex.TClose{}:
      True{}
    case other:
      False{}

# is a comma right before these tokens well placed: they are none, or their
# first may follow it?
def placed(rest: List<&2, Lex.Tok>) -> Bool:
  match rest:
    case Nil{}:
      True{}
    case Con{Lex.Tok{k, _t, _l, _c}, _more}:
      beside(k)

# is every comma well placed?
def spaced(toks: List<&2, Lex.Tok>) -> Bool:
  match toks:
    case Nil{}:
      True{}
    case Con{Lex.Tok{Lex.TComma{}, _t, _l, _c}, +rest}:
      Bool.and(placed(rest), spaced(rest))
    case Con{_tok, rest}:
      spaced(rest)

# the tokens that are no space
def unspaced(toks: List<&2, Lex.Tok>) -> List<&2, Lex.Tok>:
  match toks:
    case Nil{}:
      Nil{}
    case Con{Lex.Tok{Lex.TSpace{}, _t, _l, _c}, rest}:
      unspaced(rest)
    case Con{tok, rest}:
      tok <> unspaced(rest)

# is the first of these tokens a comment?
def noted(rest: List<&2, Lex.Tok>) -> Bool:
  match rest:
    case Nil{}:
      False{}
    case Con{Lex.Tok{Lex.TComment{}, _t, _l, _c}, _more}:
      True{}
    case Con{_tok, _more}:
      False{}

# is every space token that neither opens its line nor comes before a
# comment one space? lead: does the next token open its line?
def single(toks: List<&2, Lex.Tok>, lead: Bool) -> Bool:
  match toks:
    case Nil{}:
      True{}
    case Con{Lex.Tok{Lex.TSpace{}, t, _l, _c}, +rest}:
      Bool.and(Bool.or(lead, Bool.or(noted(rest), String.eq(t, " "))), single(rest, False{}))
    case Con{Lex.Tok{Lex.TNewline{}, _t, _l, _c}, rest}:
      single(rest, True{})
    case Con{_tok, rest}:
      single(rest, False{})

# the tokens with the text of each space token set aside
def blanked(toks: List<&2, Lex.Tok>) -> List<&2, Lex.Tok>:
  match toks:
    case Nil{}:
      Nil{}
    case Con{Lex.Tok{Lex.TSpace{}, _t, l, c}, rest}:
      Lex.Tok{Lex.TSpace{}, "", l, c} <> blanked(rest)
    case Con{tok, rest}:
      tok <> blanked(rest)

# LAW: after commas, every comma is well placed
law commas_place_every_comma:
  for toks: List<&2, Lex.Tok>
  {spaced(Line.commas(toks)) == True{} : Bool}

# LAW: tokens whose every comma is well placed come back as they are
law commas_leave_placed:
  for toks: List<&2, Lex.Tok>
  for e: {spaced(toks) == True{} : Bool}
  {Line.commas(toks) == toks : List<&2, Lex.Tok>}

# LAW: commas done twice is commas done once
law commas_twice_is_once:
  for +toks: List<&2, Lex.Tok>
  {Line.commas(Line.commas(toks)) == Line.commas(toks) : List<&2, Lex.Tok>}

# LAW: commas adds space tokens and nothing else: the tokens that are no
# space are the ones that went in, each as it was
law commas_add_only_spaces:
  for toks: List<&2, Lex.Tok>
  {unspaced(Line.commas(toks)) == unspaced(toks) : List<&2, Lex.Tok>}

# LAW: after runs, every space token that neither opens its line nor comes
# before a comment is one space, whether the tokens start a line or not
law runs_leave_one_space:
  for toks: List<&2, Lex.Tok>
  for lead: Bool
  {single(Line.runs(toks, lead), lead) == True{} : Bool}

# LAW: runs done twice is runs done once
law runs_twice_is_once:
  for toks: List<&2, Lex.Tok>
  for lead: Bool
  {Line.runs(Line.runs(toks, lead), lead) == Line.runs(toks, lead) : List<&2, Lex.Tok>}

# LAW: runs changes the text of space tokens and nothing else
law runs_change_only_space_text:
  for toks: List<&2, Lex.Tok>
  for lead: Bool
  {blanked(Line.runs(toks, lead)) == blanked(toks) : List<&2, Lex.Tok>}

# LAW: a space that opens its line is kept as written
law runs_keep_indent:
  for t: String
  for l: U32
  for c: U32
  for rest: List<&2, Lex.Tok>
  {Line.runs(Lex.Tok{Lex.TSpace{}, t, l, c} <> rest, True{})
    == Lex.Tok{Lex.TSpace{}, t, l, c} <> Line.runs(rest, False{}) : List<&2, Lex.Tok>}

# LAW: a space before a comment is kept as written, wherever on its line
law runs_keep_space_before_comment:
  for t: String
  for l: U32
  for c: U32
  for ct: String
  for cl: U32
  for cc: U32
  for rest: List<&2, Lex.Tok>
  for lead: Bool
  {Line.runs(Lex.Tok{Lex.TSpace{}, t, l, c} <> Lex.Tok{Lex.TComment{}, ct, cl, cc} <> rest, lead)
    == Lex.Tok{Lex.TSpace{}, t, l, c} <> Lex.Tok{Lex.TComment{}, ct, cl, cc} <> Line.runs(rest, False{})
    : List<&2, Lex.Tok>}
