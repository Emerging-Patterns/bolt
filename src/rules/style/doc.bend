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
import ../../role.bend as Role
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

# The flags of a file's lines. check.above reads the lines from the top for
# each item, which is the items times the lines (412 s on a generated file
# of 42,691 items). The flags hold, for every line, whether a comment block
# ends right above it, read off in one pass down the file; an item's line is
# then looked up. A binary trie on the low bits of the line number, a leaf
# holding the lines that reach it with their flags. It answers as
# check.above does, for any lines and any line asked
# (laws/DocFlagsAnswerAsLines.bend).

# a line and whether a comment block ends right above it
type Cell is Data:
  Cell{line: U32, ok: Bool}

# the flags, by the low bits of the line
type Flags is Data:
  FNone{}
  FLeaf{cells: List<&2, Cell>}
  FNode{lo: Flags, hi: Flags}

# how many bits of a line the flags branch on
def flags.depth() -> Nat:
  12n

# the cells at a leaf, none elsewhere
def flags.cells(fl: Flags) -> List<&2, Cell>:
  match fl:
    case FNone{}:
      Nil{}
    case FLeaf{cells}:
      cells
    case FNode{_lo, _hi}:
      Nil{}

# the low half for a set bit, the high half else
def flags.pick(bb: Bool, lo: Flags, hi: Flags) -> Flags:
  match bb:
    case True{}:
      lo
    case False{}:
      hi

# the half of a node a bit goes down, empty elsewhere
def flags.near(bb: Bool, fl: Flags) -> Flags:
  match fl:
    case FNode{lo, hi}:
      flags.pick(bb, lo, hi)
    case other:
      FNone{}

# a node whose half down a bit is sub, and the other half far
def flags.join(bb: Bool, sub: Flags, far: Flags) -> Flags:
  match bb:
    case True{}:
      FNode{sub, far}
    case False{}:
      FNode{far, sub}

# the flags with one more cell, down the low bits of its line, in front of
# what its leaf held
def flags.put(dd: Nat, +kk: U32, +fl: Flags, cell: Cell) -> Flags:
  match dd:
    case 0n:
      FLeaf{cell <> flags.cells(fl)}
    case 1n+p:
      flags.join(U32.is_even(kk), flags.put(p, U32.shr(kk), flags.near(U32.is_even(kk), fl), cell),
        flags.near(Bool.not(U32.is_even(kk)), fl))

# the flag of the first cell at a line among these; none there is no flag
def flags.find(cs: List<&2, Cell>, +nn: U32) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case Con{Cell{ll, ok}, rest}:
      Lazy.stop(Bool, U32.is_eq(ll, nn), ok, _u => flags.find(rest, nn))

# the flag at a line, down the low bits of a line
def flags.at(dd: Nat, +kk: U32, fl: Flags, +nn: U32) -> Bool:
  match dd:
    case 0n:
      flags.find(flags.cells(fl), nn)
    case 1n+p:
      flags.at(p, U32.shr(kk), flags.near(U32.is_even(kk), fl), nn)

# the flags of these lines, the first of them line ii, read down from ok.
# Each line is put in after the lines below it, so a line number met again
# (past the U32's end) never hides the first
def flags.build(lines: List<&2, String>, +ii: U32, +ok: Bool) -> Flags:
  match lines:
    case Nil{}:
      flags.put(flags.depth(), ii, FNone{}, Cell{ii, ok})
    case Con{hh, tt}:
      flags.put(flags.depth(), ii, flags.build(tt, U32.inc(ii), check.after(hh, ok)), Cell{ii, ok})

# the flags of a file's lines
def flags(lines: List<&2, String>) -> Flags:
  flags.build(lines, 0, False{})

# does a comment block end right above line nn? The flags' answer
def above.at(fl: Flags, +nn: U32) -> Bool:
  flags.at(flags.depth(), nn, fl, nn)

def check.fast(items: List<&2, Outline.Item>, +path: String, +fl: Flags) -> List<&2, F.Finding>:
  match items:
    case Nil{}:
      Nil{}
    case Con{Outline.Item{+k, +name, +line, _sig, _doc, _p}, rest}:
      +more = check.fast(rest, path, fl)
      Bool.pick(List<&2, F.Finding>,
        Lazy.and_then(Bool.and(needs(k), Bool.not(exempt(name))), _u => Bool.not(above.at(fl, line))),
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
    [], _u => check.fast(items, path, flags(lines(text, toks))))

# the rule, told the file's role (src/role.bend): a proof file is skipped
def check.role(rr: Role.Role, ss: Src.Src) -> List<&2, F.Finding>:
  Src.Src{+path, text, toks, tree, bound, items} = ss
  Lazy.stop(List<&2, F.Finding>, Bool.or(Role.is_proof(rr), Paths.is_test(path)),
    [], _u => check.fast(items, path, flags(lines(text, toks))))
