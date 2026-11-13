# proofs of laws/DocReportsUndocumentedItems.bend
import Base
import ../src/finding.bend as F
import ../src/paths.bend as Paths
import ../src/lazy/lazy.bend as Lazy
import ../src/syntax/outline.bend as Outline
import ../src/rules/style/doc.bend as Doc
import ../src/rules/correctness/pick.bend as Pick
import ../laws/DocReportsUndocumentedItems.bend as Laws
import ../laws/DocFlagsAnswerAsLines.bend as L1
import ./lemmas/HoleEarlyAnd.bend as M1
import ./lemmas/Nat.bend as M2
import ./lemmas/Pick.bend as M3
import ./lemmas/DocFlags.bend as M4

# doc (laws/DocReportsUndocumentedItems.bend): the rule's early exits are the law's plain picks and
# ands, so an item adds a finding exactly when the law calls it bare.

# the early exit of a Bool search is the plain pick
law doc.pick:
  for c: Bool
  for -a: Bool
  for -x: Bool
  for -y: Bool
  for ih: {x == y : Bool}
  {Lazy.stop(Bool, c, a, _u => x) == Bool.pick(Bool, c, a, y) : Bool}

def doc.pick(c, _a, _x, _y, ih):
  match c:
    case True{}:
      {==}
    case False{}:
      ih

# the read down from ok to line nn, to the rule and to the law
law doc.lead:
  for lines: List<&2, String>
  for +nn: U32
  for +ok: Bool
  {Doc.check.lead(lines, nn, ok) == Laws.doc.lead(lines, nn, ok) : Bool}

def doc.lead(lines, nn, ok):
  match lines:
    case Nil{}:
      {==}
    case Con{+hh, tt}:
      doc.pick(U32.is_eq(nn, 0), ok, Doc.check.lead(tt, U32.sub(nn, 1), Doc.check.after(hh, ok)),
        Laws.doc.lead(tt, U32.sub(nn, 1), Laws.doc.after(hh, ok)),
        doc.lead(tt, U32.sub(nn, 1), Doc.check.after(hh, ok)))

# the comment block above line nn, to the rule and to the law
law doc.above:
  for +lines: List<&2, String>
  for +nn: U32
  {Doc.check.above(lines, nn) == Laws.doc.lead(lines, nn, False{}) : Bool}

def doc.above(lines, nn):
  doc.lead(lines, nn, False{})

# the kind and name test, to the rule and to the law
law doc.needs:
  for kk: Outline.ItemKind
  for +name: String
  {Bool.and(Doc.needs(kk), Bool.not(Doc.exempt(name))) == Bool.and(Laws.doc.kind(kk), Bool.not(Laws.doc.free(name)))
    : Bool}

def doc.needs(kk, _name):
  match kk:
    case Outline.IImport{}:
      {==}
    case Outline.IDef{}:
      {==}
    case Outline.ILaw{}:
      {==}
    case Outline.IType{}:
      {==}
    case Outline.ICtor{}:
      {==}
    case Outline.ILocal{}:
      {==}

# an item's hit, to the rule and to the law
law doc.hit:
  for +kk: Outline.ItemKind
  for +name: String
  for +line: U32
  for +doc: String
  for +lines: List<&2, String>
  {Lazy.and_then(Bool.and(Doc.needs(kk), Bool.not(Doc.exempt(name))), _u => Bool.not(Doc.check.above(lines, line)))
    == Laws.doc.bare(kk, name, line, doc, lines) : Bool}

def doc.hit(kk, name, line, _doc, lines):
  +ar = Bool.and(Doc.needs(kk), Bool.not(Doc.exempt(name)))
  +as = Bool.and(Laws.doc.kind(kk), Bool.not(Laws.doc.free(name)))
  +ns = Bool.not(Laws.doc.lead(lines, line, False{}))
  Equal.trans(Bool, Lazy.and_then(ar, _u => Bool.not(Doc.check.above(lines, line))), Bool.and(ar, ns),
    Bool.and(as, ns),
    M1.hole.and(ar, Bool.not(Doc.check.above(lines, line)), ns,
      Equal.cong(Bool, Bool, z => Bool.not(z), Doc.check.above(lines, line),
        Laws.doc.lead(lines, line, False{}), doc.above(lines, line))),
    Equal.cong(Bool, Bool, z => Bool.and(z, ns), ar, as, doc.needs(kk, name)))

# an item onto a rest the law holds for
law doc.item:
  for +kk: Outline.ItemKind
  for +name: String
  for +line: U32
  for sig: String
  for +doc: String
  for pp: String
  for +rest: List<&2, Outline.Item>
  for +path: String
  for +lines: List<&2, String>
  for ih: {List.length(&2, F.Finding, Doc.check.go(rest, path, lines)) == Laws.doc.count(rest, lines) : Nat}
  {List.length(&2, F.Finding, Doc.check.go(Outline.Item{kk, name, line, sig, doc, pp} <> rest, path, lines))
    == Laws.doc.count(Outline.Item{kk, name, line, sig, doc, pp} <> rest, lines) : Nat}

def doc.item(kk, name, line, _sig, doc, _pp, rest, path, lines, ih):
  +more = Doc.check.go(rest, path, lines)
  +m = Laws.doc.count(rest, lines)
  +x = {F.Finding{path, line, 0, 0, "doc", Doc.what(kk) ++ " " ++ name ++ " has no comment above it."} : F.Finding}
  +hr = Lazy.and_then(Bool.and(Doc.needs(kk), Bool.not(Doc.exempt(name))), _u => Bool.not(Doc.check.above(lines, line)))
  +hs = Laws.doc.bare(kk, name, line, doc, lines)
  Equal.trans(Nat, List.length(&2, F.Finding, Bool.pick(List<&2, F.Finding>, hr, x <> more, more)),
    List.length(&2, F.Finding, Bool.pick(List<&2, F.Finding>, hs, x <> more, more)),
    Bool.pick(Nat, hs, 1n+m, m),
    Equal.cong(Bool, Nat, z => List.length(&2, F.Finding, Bool.pick(List<&2, F.Finding>, z, x <> more, more)), hr, hs,
      doc.hit(kk, name, line, doc, lines)),
    M2.nat.pick(hs, x, more, m, ih))

def Laws.doc_walk_counts(items, path, lines):
  match items:
    case Nil{}:
      {==}
    case Con{it, +rest}:
      match it:
        case Outline.Item{kk, name, line, sig, doc, pp}:
          doc.item(kk, name, line, sig, doc, pp, rest, path, lines, Laws.doc_walk_counts(rest, path, lines))

def Laws.doc_counts(path, text, toks, _tree, _bound, items):
  +ls = Doc.lines(text, toks)
  +fast = Doc.check.fast(items, path, Doc.flags(ls))
  +slow = Doc.check.go(items, path, ls)
  M3.param.stop(Bool.or(Paths.is_proof(path), Paths.is_test(path)), fast, Laws.doc.count(items, ls),
    Equal.trans(Nat, List.length(&2, F.Finding, fast), List.length(&2, F.Finding, slow), Laws.doc.count(items, ls),
      Equal.cong(List<&2, F.Finding>, Nat, z => List.length(&2, F.Finding, z), fast, slow,
        L1.fast_is_go(items, path, ls)),
      Laws.doc_walk_counts(items, path, ls)))

def Laws.doc_lines_inside_are_text(_hh, _tt, _ins):
  {==}

def Laws.doc_lines_of_text(_text, _toks):
  {==}
