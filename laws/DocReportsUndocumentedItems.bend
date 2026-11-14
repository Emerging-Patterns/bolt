# `doc` reports exactly a top-level def, type or law with no comment block
# right above it, or right above a run of `@` lines (attributes such as
# `@unsafe`) right above it, with the header's exemptions.
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/syntax/bind.bend as Bind
import ../src/paths.bend as Paths
import ../src/src.bend as Src
import ../src/syntax/tree.bend as Tree
import ../src/syntax/outline.bend as Outline
import ../src/rules/style/doc.bend as Doc

# doc (laws/DocReportsUndocumentedItems.bend). Over the outline's items the rule reports each def,
# type and law with no comment block right above it: reading up from the
# item past any lines that start with `@` (attributes such as `@unsafe`),
# the first other line does not start with `#` (a block of bare `#` lines
# counts; its doc text is never read). The header's exemptions: a name that
# is `main` or holds a dot (a helper), and a PROOF.bend or a file under a
# `tests` directory.

# a def, a type or a law: the kinds that need a comment
def doc.kind(k: Outline.ItemKind) -> Bool:
  match k:
    case Outline.IDef{}:
      True{}
    case Outline.IType{}:
      True{}
    case Outline.ILaw{}:
      True{}
    case other:
      False{}

# `main`, or a helper: a name holding a dot
def doc.free(+name: String) -> Bool:
  Bool.or(String.eq(name, "main"), String.contains(name, "."))

# reading down, does a comment block end right above the next line? After a
# `#` line it does; an `@` line keeps what was above it; any other line ends it
def doc.after(+line: String, ok: Bool) -> Bool:
  Bool.or(String.starts_with(line, "#"), Bool.and(String.starts_with(line, "@"), ok))

# reading lines 0 to n - 1 (0-based) down from ok: does a comment block end
# right above line n, past a run of `@` lines?
def doc.lead(lines: List<&2, String>, +n: U32, +ok: Bool) -> Bool:
  match lines:
    case Nil{}:
      Bool.and(U32.is_eq(n, 0), ok)
    case Con{h, t}:
      Bool.pick(Bool, U32.is_eq(n, 0), ok, doc.lead(t, U32.sub(n, 1), doc.after(h, ok)))

# an item that needs a comment and has none: an unexempt def, type or law
# with no `#` line right above it, or right above the `@` lines right above
# it (its doc text is never read)
def doc.bare(k: Outline.ItemKind, +name: String, +line: U32, _doc: String, +lines: List<&2, String>) -> Bool:
  Bool.and(Bool.and(doc.kind(k), Bool.not(doc.free(name))), Bool.not(doc.lead(lines, line, False{})))

# how many items need a comment and have none
def doc.count(items: List<&2, Outline.Item>, +lines: List<&2, String>) -> Nat:
  match items:
    case Nil{}:
      0n
    case Con{Outline.Item{k, +name, +line, sig, +doc, p}, rest}:
      +m = doc.count(rest, lines)
      Bool.pick(Nat, doc.bare(k, name, line, doc, lines), 1n+m, m)

# LAW: over the outline's items, doc reports one finding for each def, type
# or law not named `main` and holding no dot whose line has no `#` line
# right above it, or right above a run of `@` lines right above it, and none
# for any other item
law doc_walk_counts:
  for items: List<&2, Outline.Item>
  for +path: String
  for +lines: List<&2, String>
  {List.length(&2, F.Finding, Doc.check.go(items, path, lines)) == doc.count(items, lines) : Nat}

# LAW: doc reports exactly those items of the file, read against its lines
# (a line that starts inside a string literal read as empty), and nothing in
# a PROOF.bend or a file under a `tests` directory
law doc_counts:
  for +path: String
  for +text: String
  for +toks: List<&2, Lex.Tok>
  for tree: Tree.Node
  for bound: Bind.Bound
  for +items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Doc.check(Src.Src{path, text, toks, tree, bound, items}))
    == Bool.pick(Nat, Bool.or(Paths.is_proof(path), Paths.is_test(path)), 0n, doc.count(items, Doc.lines(text, toks)))
    : Nat}

# LAW: reading the lines beside the lexer's word on each (does it start
# inside a string literal?), such a line is read as empty, so it is never a
# comment line, and any other line is read as it is, in order
law doc_lines_inside_are_text:
  for h: String
  for t: List<&2, String>
  for +ins: List<&2, Bool>
  {Doc.lines.go(h <> t, ins)
    == Bool.pick(String, Outline.inside.hit(ins), "", h) <> Doc.lines.go(t, Outline.inside.rest(ins))
    : List<&2, String>}

# LAW: the lines doc reads are the text's lines beside what the tokens say
# of each
law doc_lines_of_text:
  for text: String
  for toks: List<&2, Lex.Tok>
  {Doc.lines(text, toks) == Doc.lines.go(String.lines(text), Outline.inside(toks)) : List<&2, String>}
