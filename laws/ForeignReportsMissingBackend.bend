# `foreign` reports exactly a foreign def with a `.c` body and no `.js` or the
# reverse, where a file whose leading comment lines include the exact line `#
# lanes: native` needs no `.js`. A def's body is what is under its whole
# header, wrapped over lines or not (laws/DefSignatureRunsToItsColon.bend).
#
# also rests on: laws/DefSignatureRunsToItsColon.bend
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/syntax/bind.bend as Bind
import ../src/src.bend as Src
import ../src/syntax/tree.bend as Tree
import ../src/syntax/outline.bend as Outline
import ../src/rules/pedantic/foreign.bend as Foreign
import ../src/rules/calls.bend as Calls

# foreign (laws/ForeignReportsMissingBackend.bend). Over the file's top-level statements the rule
# reports each def whose body (Calls.under: the statements under it, less the
# lines its header wrapped onto) is one import or more and nothing else (a
# foreign def) and whose imports name a `.c` body and no `.js` one, unless the
# file is headed `# lanes: native`, or a `.js` body and no `.c` one. Headed
# means the exact line is among the file's leading comment lines, those before
# its first line that does not start with `#`. An import's path is its first
# string literal (Foreign.target).

# every statement of the body is an import, none at all included
def foreign.imports(body: Tree.Node) -> Bool:
  match body:
    case Tree.NCons{Tree.Stmt{Tree.SImport{}, kids, ib}, rest}:
      foreign.imports(rest)
    case Tree.NCons{h, rest}:
      False{}
    case other:
      True{}

# a foreign def's body: one import or more, and nothing else
def foreign.only(body: Tree.Node) -> Bool:
  match body:
    case Tree.NCons{Tree.Stmt{Tree.SImport{}, kids, ib}, rest}:
      foreign.imports(rest)
    case other:
      False{}

# some import of the body names a path ending in the suffix (quoted: `.c"`)
def foreign.has(body: Tree.Node, +ext: String) -> Bool:
  match body:
    case Tree.NCons{Tree.Stmt{Tree.SImport{}, kids, ib}, rest}:
      Bool.or(String.ends_with(Foreign.target(kids), ext), foreign.has(rest, ext))
    case Tree.NCons{h, rest}:
      foreign.has(rest, ext)
    case other:
      False{}

# a foreign def with a `.c` body and no `.js` one (in a file not native only),
# or with a `.js` body and no `.c` one
def foreign.bad(+body: Tree.Node, +native: Bool) -> Bool:
  +c = foreign.has(body, ".c\"")
  +js = foreign.has(body, ".js\"")
  Bool.and(foreign.only(body),
    Bool.or(Bool.and(c, Bool.and(Bool.not(js), Bool.not(native))), Bool.and(js, Bool.not(c))))

# how many of the file's top-level defs are foreign defs missing a lane
def foreign.count(root: Tree.Node, +native: Bool) -> Nat:
  match root:
    case Tree.NCons{Tree.Stmt{Tree.SDef{}, kids, body}, rest}:
      +m = foreign.count(rest, native)
      Bool.pick(Nat, foreign.bad(Calls.under(kids, body), native), 1n+m, m)
    case Tree.NCons{h, rest}:
      foreign.count(rest, native)
    case other:
      0n

# the exact line `# lanes: native` is among the leading lines that start with `#`
def foreign.headed(lines: List<&2, String>) -> Bool:
  match lines:
    case Nil{}:
      False{}
    case Con{+line, rest}:
      Bool.and(String.starts_with(line, "#"), Bool.or(String.eq(line, "# lanes: native"), foreign.headed(rest)))

# LAW: a file is native only exactly when the line `# lanes: native` is one
# of its leading comment lines; the line anywhere later does not count
law foreign_native:
  for lines: List<&2, String>
  {Foreign.native_only.go(lines) == foreign.headed(lines) : Bool}

# LAW: over the file's top-level statements, foreign reports one finding for
# each foreign def with a `.c` body and no `.js` one (none needed in a native
# only file) or a `.js` body and no `.c` one, and none for anything else
law foreign_walk_counts:
  for root: Tree.Node
  for +native: Bool
  for +path: String
  {List.length(&2, F.Finding, Foreign.check.go(root, native, path)) == foreign.count(root, native) : Nat}

# LAW: foreign reports exactly those defs of the file, native only when its
# leading comment lines say so
law foreign_counts:
  for +path: String
  for +text: String
  for toks: List<&2, Lex.Tok>
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Foreign.check(Src.Src{path, text, toks, tree, bound, items}))
    == foreign.count(tree, foreign.headed(String.lines(text))) : Nat}
