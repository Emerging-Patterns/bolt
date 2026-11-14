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
def needs(k: Outline.ItemKind) -> Bool:
  match k:
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
def what(k: Outline.ItemKind) -> String:
  match k:
    case Outline.IType{}:
      "Type"
    case Outline.ILaw{}:
      "Law"
    case other:
      "Def"

# reading down, does a comment block end right above the next line? After a
# comment line (its first char `#`) it does; an attribute line (`@unsafe`)
# keeps what was above it; any other line ends it
def check.after(+h: String, ok: Bool) -> Bool:
  Bool.or(String.starts_with(h, "#"), Bool.and(String.starts_with(h, "@"), ok))

# reading lines 0 to n - 1 down from ok: does a comment block end right
# above line n, past a run of attribute lines?
def check.lead(lines: List<&2, String>, +n: U32, +ok: Bool) -> Bool:
  match lines:
    case Nil{}:
      Bool.and(U32.is_eq(n, 0), ok)
    case Con{h, t}:
      Lazy.stop(Bool, U32.is_eq(n, 0), ok, _u => check.lead(t, U32.sub(n, 1), check.after(h, ok)))

# is there a comment line right above line n, or right above the attribute
# lines right above it? A block of bare `#` lines counts, though its doc text
# is empty. An item's comment block always ends there, so this test alone
# decides: the doc text, what the comments say, is never read
def check.above(+lines: List<&2, String>, +n: U32) -> Bool:
  check.lead(lines, n, False{})

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
def flags.pick(b: Bool, lo: Flags, hi: Flags) -> Flags:
  match b:
    case True{}:
      lo
    case False{}:
      hi

# the half of a node a bit goes down, empty elsewhere
def flags.near(b: Bool, fl: Flags) -> Flags:
  match fl:
    case FNode{lo, hi}:
      flags.pick(b, lo, hi)
    case other:
      FNone{}

# a node whose half down a bit is sub, and the other half far
def flags.join(b: Bool, sub: Flags, far: Flags) -> Flags:
  match b:
    case True{}:
      FNode{sub, far}
    case False{}:
      FNode{far, sub}

# the flags with one more cell, down the low bits of its line, in front of
# what its leaf held
def flags.put(d: Nat, +k: U32, +fl: Flags, cell: Cell) -> Flags:
  match d:
    case 0n:
      FLeaf{cell <> flags.cells(fl)}
    case 1n+p:
      flags.join(U32.is_even(k), flags.put(p, U32.shr(k), flags.near(U32.is_even(k), fl), cell),
        flags.near(Bool.not(U32.is_even(k)), fl))

# the flag of the first cell at a line among these; none there is no flag
def flags.find(cs: List<&2, Cell>, +n: U32) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case Con{Cell{l, ok}, rest}:
      Lazy.stop(Bool, U32.is_eq(l, n), ok, _u => flags.find(rest, n))

# the flag at a line, down the low bits of a line
def flags.at(d: Nat, +k: U32, fl: Flags, +nn: U32) -> Bool:
  match d:
    case 0n:
      flags.find(flags.cells(fl), nn)
    case 1n+p:
      flags.at(p, U32.shr(k), flags.near(U32.is_even(k), fl), nn)

# the flags of these lines, the first of them line i, read down from ok.
# Each line is put in after the lines below it, so a line number met again
# (past the U32's end) never hides the first
def flags.build(lines: List<&2, String>, +i: U32, +ok: Bool) -> Flags:
  match lines:
    case Nil{}:
      flags.put(flags.depth(), i, FNone{}, Cell{i, ok})
    case Con{h, t}:
      flags.put(flags.depth(), i, flags.build(t, U32.inc(i), check.after(h, ok)), Cell{i, ok})

# the flags of a file's lines
def flags(lines: List<&2, String>) -> Flags:
  flags.build(lines, 0, False{})

# does a comment block end right above line n? The flags' answer
def above.at(fl: Flags, +n: U32) -> Bool:
  flags.at(flags.depth(), n, fl, n)

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
    case Con{h, t}:
      Bool.pick(String, Outline.inside.hit(ins), "", h) <> lines.go(t, Outline.inside.rest(ins))

# the lines of a source, each one that starts inside a string literal read
# as empty: it is text, never a comment line
def lines(text: String, toks: List<&2, Lex.Tok>) -> List<&2, String>:
  lines.go(String.lines(text), Outline.inside(toks))

# the rule
def check(s: Src.Src) -> List<&2, F.Finding>:
  Src.Src{+path, text, toks, tree, bound, items} = s
  Lazy.stop(List<&2, F.Finding>, Bool.or(Paths.is_proof(path), Paths.is_test(path)),
    [], _u => check.fast(items, path, flags(lines(text, toks))))

# the rule, told the file's role (src/role.bend): a proof file is skipped
def check.role(r: Role.Role, s: Src.Src) -> List<&2, F.Finding>:
  Src.Src{+path, text, toks, tree, bound, items} = s
  Lazy.stop(List<&2, F.Finding>, Bool.or(Role.is_proof(r), Paths.is_test(path)),
    [], _u => check.fast(items, path, flags(lines(text, toks))))
