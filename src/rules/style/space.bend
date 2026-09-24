# rule space: trailing whitespace, a tab, or a line over 120 characters. The
# width counts a string literal as two characters: a long message or a test
# fixture does not make a line hard to read, code does. A comment counts at
# its full width. Expectation trailers (`#|` lines) are data and exempt from
# the width only: trailing whitespace on a `#|` line is still reported. A tab
# is reported wherever it sits, inside a string literal included. A line
# with both trailing whitespace and a tab is reported once, for the
# whitespace.
import Base
import ../../src.bend as Src
import ../../finding.bend as F
import ../../syntax/lex.bend as Lex
import ../../lazy/lazy.bend as Lazy

# is there a tab among the chars?
def has_tab(cs: List<&2, Char>) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case Con{c, t}:
      Lazy.or_else(Char.is_eq(c, '\t'), _u => has_tab(t))

# does the line end in whitespace?
def trailing(cs: List<&2, Char>) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case Con{c, Nil{}}:
      Char.is_space(c)
    case Con{c, t}:
      trailing(t)

# a token's share of its line's width; a `#|` trailer line counts nothing
def width_of(kk: Lex.TokKind, +tt: String) -> U32:
  match kk:
    case Lex.TStr{}:
      2
    case Lex.TNewline{}:
      0
    case Lex.TComment{}:
      Bool.pick(U32, String.starts_with(tt, "#|"), 0, U32.from_nat(String.length(tt)))
    case other:
      U32.from_nat(String.length(tt))

# a finding when the width is over 120
def too_wide(+width: U32, +path: String, +nn: U32, +more: List<&2, F.Finding>) -> List<&2, F.Finding>:
  Bool.pick(List<&2, F.Finding>, U32.is_gt(width, 120),
    F.Finding{path, nn, 120, 0, "space", "Line is longer than 120 characters."} <> more, more)

# one pass over the tokens: a newline closes a line's width
def widths(toks: List<&2, Lex.Tok>, +path: String, +nn: U32, +acc: U32) -> List<&2, F.Finding>:
  match toks:
    case Nil{}:
      too_wide(acc, path, nn, [])
    case Con{Lex.Tok{Lex.TNewline{}, t, l, c}, rest}:
      too_wide(acc, path, nn, widths(rest, path, (nn + 1 : U32), 0))
    case Con{Lex.Tok{k, t, l, c}, rest}:
      +w = width_of(k, t)
      widths(rest, path, nn, (acc + w : U32))

def check.line(+path: String, +nn: U32, +cs: List<&2, Char>, +more: List<&2, F.Finding>) -> List<&2, F.Finding>:
  +len = U32.from_nat(List.length(&2, Char, cs))
  Bool.pick(List<&2, F.Finding>, trailing(cs),
    F.Finding{path, nn, (len - 1 : U32), 1, "space", "Line has trailing whitespace."} <> more,
    Bool.pick(List<&2, F.Finding>, has_tab(cs),
      F.Finding{path, nn, 0, 1, "space", "Line contains a tab; indent with spaces."} <> more, more))

def check.go(lines: List<&2, String>, +path: String, +nn: U32) -> List<&2, F.Finding>:
  match lines:
    case Nil{}:
      Nil{}
    case Con{line, rest}:
      check.line(path, nn, String.to_list(line), check.go(rest, path, (nn + 1 : U32)))

# the rule
def check(ss: Src.Src) -> List<&2, F.Finding>:
  Src.Src{+path, text, toks, tree, bound, items} = ss
  List.append(&2, F.Finding, check.go(String.lines(text), path, 0), widths(toks, path, 0, 0))
