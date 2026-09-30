# rule doc: every top-level def, type and law has a comment block right above
# it: one or more column-0 `#` lines with no blank line between them and the
# item, save a run of column-0 `@` lines (attributes such as `@unsafe`) that
# may sit between the block and the item. A block of bare `#` lines counts,
# though its text is empty; a line that starts inside a multi-line string
# literal is text, never a comment line. Helpers
# (dotted names like `show.go`) ride on their parent's doc, `main` needs none,
# PROOF.bend fills laws that LAWS.bend already documents, and a test (under
# tests/) is documented by its header and its check names.
import Base
import ../../src.bend as Src
import ../../finding.bend as F
import ../../syntax/outline.bend as Outline
import ../../lazy/lazy.bend as Lazy
import ../../paths.bend as Paths
import ../../syntax/lex.bend as Lex

# does an item of this kind need a comment?
def needs(kk: Outline.ItemKind) -> Bool:
  match kk:
    case Outline.IDef{}:
      True{}
    case Outline.IType{}:
      True{}
    case Outline.ILaw{}:
      True{}
    case other:
      False{}

# `main`, and helpers named `x.go`
def exempt(+name: String) -> Bool:
  Bool.or(String.eq(name, "main"), String.contains(name, "."))

# an item's kind, for the message
def what(kk: Outline.ItemKind) -> String:
  match kk:
    case Outline.IType{}:
      "Type"
    case Outline.ILaw{}:
      "Law"
    case other:
      "Def"

# reading down, does a comment block end right above the next line? After a
# comment line (its first char `#`) it does; an attribute line (`@unsafe`)
# keeps what was above it; any other line ends it
def check.after(+hh: String, ok: Bool) -> Bool:
  Bool.or(String.starts_with(hh, "#"), Bool.and(String.starts_with(hh, "@"), ok))

# reading lines 0 to nn - 1 down from ok: does a comment block end right
# above line nn, past a run of attribute lines?
def check.lead(lines: List<&2, String>, +nn: U32, +ok: Bool) -> Bool:
  match lines:
    case Nil{}:
      Bool.and(U32.is_eq(nn, 0), ok)
    case Con{hh, tt}:
      Lazy.stop(Bool, U32.is_eq(nn, 0), ok, _u => check.lead(tt, U32.sub(nn, 1), check.after(hh, ok)))

# is there a comment line right above line nn, or right above the attribute
# lines right above it? A block of bare `#` lines counts, though its doc text
# is empty. An item's comment block always ends there, so this test alone
# decides: the doc text, what the comments say, is never read
def check.above(+lines: List<&2, String>, +nn: U32) -> Bool:
  check.lead(lines, nn, False{})

def check.go(items: List<&2, Outline.Item>, +path: String, +lines: List<&2, String>) -> List<&2, F.Finding>:
  match items:
    case Nil{}:
      Nil{}
    case Con{Outline.Item{+k, +name, +line, _sig, _doc, _p}, rest}:
      +more = check.go(rest, path, lines)
      Bool.pick(List<&2, F.Finding>,
        Lazy.and_then(Bool.and(needs(k), Bool.not(exempt(name))), _u => Bool.not(check.above(lines, line))),
        F.Finding{path, line, 0, 0, "doc", what(k) ++ " " ++ name ++ " has no comment above it."} <> more, more)

def lines.go(ls: List<&2, String>, +ins: List<&2, Bool>) -> List<&2, String>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{hh, tt}:
      Bool.pick(String, Outline.inside.hit(ins), "", hh) <> lines.go(tt, Outline.inside.rest(ins))

# the lines of a source, each one that starts inside a string literal read
# as empty: it is text, never a comment line
def lines(text: String, toks: List<&2, Lex.Tok>) -> List<&2, String>:
  lines.go(String.lines(text), Outline.inside(toks))

# the rule
def check(ss: Src.Src) -> List<&2, F.Finding>:
  Src.Src{+path, text, toks, tree, bound, items} = ss
  Lazy.stop(List<&2, F.Finding>, Bool.or(Paths.is_proof(path), Paths.is_test(path)),
    [], _u => check.go(items, path, lines(text, toks)))
