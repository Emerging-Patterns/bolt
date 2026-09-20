# rule space: trailing whitespace, a tab, or a line over 120 characters. The
# width counts a string literal as two characters: a long message or a test
# fixture does not make a line hard to read, code does. Expectation trailers
# (`#|` lines) are data and exempt.
import Base
import ../../src.bend as Src
import ../../finding.bend as F
import ../../../syntax/lex.bend as Lex

# is there a tab among the chars?
def has_tab(cs: List<&2, Char>) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case Con{'\t', t}:
      True{}
    case Con{c, t}:
      has_tab(t)

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
def width_of(k: Lex.TokKind, +t: String) -> U32:
  match k:
    case Lex.TStr{}:
      2
    case Lex.TNewline{}:
      0
    case Lex.TComment{}:
      Bool.pick(U32, String.starts_with(t, "#|"), 0, U32.from_nat(String.length(t)))
    case other:
      U32.from_nat(String.length(t))

# a finding when the width is over 120
def too_wide(+width: U32, +path: String, +n: U32, +more: List<&2, F.Finding>) -> List<&2, F.Finding>:
  Bool.pick(List<&2, F.Finding>, U32.is_gt(width, 120), F.Finding{path, n, 120, 0, "space", "over 120 characters wide"} <> more, more)

# one pass over the tokens: a newline closes a line's width
def widths(toks: List<&2, Lex.Tok>, +path: String, +n: U32, +acc: U32) -> List<&2, F.Finding>:
  match toks:
    case Nil{}:
      too_wide(acc, path, n, [])
    case Con{Lex.Tok{Lex.TNewline{}, t, l, c}, rest}:
      too_wide(acc, path, n, widths(rest, path, (n + 1 : U32), 0))
    case Con{Lex.Tok{k, t, l, c}, rest}:
      widths(rest, path, n, (acc + width_of(k, t) : U32))

def check.line(+path: String, +n: U32, +cs: List<&2, Char>, +more: List<&2, F.Finding>) -> List<&2, F.Finding>:
  +len = U32.from_nat(List.length(&2, Char, cs))
  Bool.pick(List<&2, F.Finding>, trailing(cs), F.Finding{path, n, (len - 1 : U32), 1, "space", "trailing whitespace"} <> more,
    Bool.pick(List<&2, F.Finding>, has_tab(cs), F.Finding{path, n, 0, 1, "space", "a tab; indent with spaces"} <> more, more))

def check.go(lines: List<&2, String>, +path: String, +n: U32) -> List<&2, F.Finding>:
  match lines:
    case Nil{}:
      Nil{}
    case Con{line, rest}:
      check.line(path, n, String.to_list(line), check.go(rest, path, (n + 1 : U32)))

# the rule
def check(s: Src.Src) -> List<&2, F.Finding>:
  Src.Src{+path, text, toks, tree, bound, items} = s
  List.append(&2, F.Finding, check.go(String.lines(text), path, 0), widths(toks, path, 0, 0))
