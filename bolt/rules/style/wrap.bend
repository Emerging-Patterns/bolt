# rule wrap: a one-line def header wider than 120. The width is the header
# through its `:`, counted the way `space` counts a line: a string literal is
# two characters. A header that already spans lines is wrapped. How many
# parameters it has does not matter: a one-line header that fits stays one line.
import Base
import ../../src.bend as Src
import ../../finding.bend as F
import ../../../syntax/lex.bend as Lex
import ../../../syntax/outline.bend as Outline
import ./space.bend as Space

# the header already breaks across lines
def check.broken(+sig: String) -> Bool:
  String.contains(sig, "\n")

# one token's share of the header's width
def check.add(+acc: U32, kd: Lex.TokKind, +tx: String) -> U32:
  (acc + Space.width_of(kd, tx) : U32)

# the header's width, a string literal counting as two
def check.width.go(toks: List<&2, Lex.Tok>, +acc: U32) -> U32:
  match toks:
    case Nil{}:
      acc
    case Con{Lex.Tok{kd, tx, ln, cl}, rest}:
      check.width.go(rest, check.add(acc, kd, tx))

# the header's width
def check.width(+sig: String) -> U32:
  check.width.go(Lex.tokens(sig), 0)

# a one-line header past 120
def check.over(kk: Outline.ItemKind, +sig: String) -> Bool:
  Bool.and(Outline.is_def(kk), Bool.and(Bool.not(check.broken(sig)), U32.is_gt(check.width(sig), 120)))

def check.go(items: List<&2, Outline.Item>, +path: String) -> List<&2, F.Finding>:
  match items:
    case Nil{}:
      Nil{}
    case Con{Outline.Item{k, name, +line, +sig, doc, p}, rest}:
      +more = check.go(rest, path)
      Bool.pick(List<&2, F.Finding>, check.over(k, sig),
        F.Finding{path, line, 120, 0, "wrap", "def header over 120 characters wide"} <> more, more)

# the rule
def check(ss: Src.Src) -> List<&2, F.Finding>:
  Src.Src{+path, text, toks, tree, bound, items} = ss
  check.go(items, path)
