# In every file under a law directory, except helpers, law files and tests,
# every def and type, less the defs that are proofs, is named by a quantified
# law in a LAWS.bend or reached from one through calls. A quantified law names
# an item by a use in its statement that the binder (laws/BinderResolvesInnermostFirst.bend) resolves to
# that item, through an import alias or in the same file; a def calls an item
# by such a use on its own lines. A def is covered when such a law names it or
# a covered def calls it, in its own file or in another file of its package
# (laws/ScopePackageRootsFound.bend); a type is covered when such a law or a covered def names it
# or one of its constructors. A def that is a proof (one whose signature
# returns a proof, `-> {a == b : T}`, or one written with no type at all, as
# laws/ExemptPathsYieldNoFindings.bend reads it) is neither graded nor an item the reach passes
# through: it is how Bend fills a law, so the law states its property. Its
# signature is its whole header, wrapped over lines or not.
#
# also rests on: laws/PackagesScoped.bend, laws/DefSignatureRunsToItsColon.bend
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/syntax/bind.bend as Bind
import ../src/paths.bend as Paths
import ../src/rules/digest.bend as Digest
import ../src/src.bend as Src
import ../src/syntax/tree.bend as Tree
import ../src/syntax/outline.bend as Outline
import ../src/rules/calls.bend as Calls
import ../src/rules/laws/closed.bend as Closed
import ../src/rules/laws/law.bend as Coverage
import ../src/rules/imports.bend as Imports
import ../src/role.bend as Role
import ./defs/Unsafe.bend as D1

# coverage (laws/LawNamesEveryItem.bend). The rule reads the digests of the files in the run
# (src/rules/digest.bend), and so do its laws, coverage_reach and the
# others at the end of this file: they hold for every list of digests. Under
# law is every file of the run when one of them is a LAWS.bend
# (laws/ScopeLawsGovernPackage.bend), else none.

# some digest is a LAWS.bend
def coverage.lawful(ds: List<&2, Digest.Digest>) -> Bool:
  match ds:
    case Nil{}:
      False{}
    case Con{Digest.Digest{path, norm, dir, is_laws, is_law_file, exempt, tops, says, deps, laws}, rest}:
      Bool.or(is_laws, coverage.lawful(rest))

# coverage's reading of a file (laws/LawNamesEveryItem.bend). reach_digest and reach_binder,
# at the end of this file, state the digest of every file with these: what
# its laws name is the binder's (laws/BinderResolvesInnermostFirst.bend) resolution of each use in the
# statement of a quantified law of a LAWS.bend. A use the binder resolves to
# an item of the file is a mention of that item of the law's own file; one it
# resolves through an import alias is a mention of the item of the file that
# import names. A binder, a free name (Base, or unknown), the law's own name
# (a binder), and every use in a closed law name nothing. So a type counts as
# named only when a law uses it or one of its constructors: a use of another
# def of its file is a mention of that def, never of the type.

# the constructors the outline lists right after a type, up to the next
# item that is not one
def coverage.ctors_of(items: List<&2, Outline.Item>) -> List<&2, String>:
  match items:
    case Con{Outline.Item{Outline.ICtor{}, name, _line, _sig, _doc, _path}, rest}:
      name <> coverage.ctors_of(rest)
    case _other:
      []

# the file the first import of this alias names, resolved against the
# importing file
def coverage.alias(items: List<&2, Outline.Item>, +name: String, +from: String) -> Maybe<&2, String>:
  match items:
    case Nil{}:
      None{}
    case Con{Outline.Item{Outline.IImport{}, +nm, _line, _sig, _doc, +path}, rest}:
      +more = coverage.alias(rest, name, from)
      Bool.pick(Maybe<&2, String>, String.eq(nm, name), Some{Imports.resolve(from, path)}, more)
    case Con{_other, rest}:
      coverage.alias(rest, name, from)

# the item behind an alias, when an import names it
def coverage.behind(mm: Maybe<&2, String>, name: String) -> List<&2, Digest.Mention>:
  match mm:
    case None{}:
      []
    case Some{pp}:
      [Digest.Mention{pp, name}]

# what a use the binder resolved names: an item of the file, or an item
# behind an import alias; a binder or a free name names nothing
def coverage.target(tt: Bind.Target, items: List<&2, Outline.Item>, +file: String) -> List<&2, Digest.Mention>:
  match tt:
    case Bind.TItem{name}:
      [Digest.Mention{file, name}]
    case Bind.TQual{al, name}:
      coverage.behind(coverage.alias(items, al, file), name)
    case _other:
      []

# is the line on the statement of a quantified law of the tree: from its
# header's first token to its body's last?
def coverage.in_law(root: Tree.Node, +ln: U32) -> Bool:
  match root:
    case Tree.NCons{Tree.Stmt{Tree.SLaw{}, kids, +body}, rest}:
      Bool.or(Bool.and(Closed.binds(body), Bool.and(U32.is_le(Tree.line(kids), ln),
        U32.is_le(ln, Tree.line.of(List.head(&2, Lex.Tok, Tree.leaves.go(body, [])))))), coverage.in_law(rest, ln))
    case Tree.NCons{_h, rest}:
      coverage.in_law(rest, ln)
    case _other:
      False{}

# what the uses on the quantified laws' statements name, in order
def coverage.said(
  us: List<&2, Bind.Use>,
  +root: Tree.Node,
  +items: List<&2, Outline.Item>,
  +file: String
) -> List<&2, Digest.Mention>:
  match us:
    case Nil{}:
      []
    case Con{Bind.Use{_n, ln, _c, tt}, rest}:
      +more = coverage.said(rest, root, items, file)
      Bool.pick(List<&2, Digest.Mention>, coverage.in_law(root, ln),
        List.append(&2, Digest.Mention, coverage.target(tt, items, file), more), more)

# the uses the binder recorded
def coverage.uses(bb: Bind.Bound) -> List<&2, Bind.Use>:
  match bb:
    case Bind.Bound{_bs, us, _scs}:
      us

# what the coverage rule reads of a digest
type CoverageView is Data:
  CoverageView{norm: String, is_laws: Bool, exempt: Bool, tops: List<&2, Digest.Top>, says: List<&2, Digest.Mention>}

# a digest as the coverage rule reads it
def coverage.view(dd: Digest.Digest) -> CoverageView:
  match dd:
    case Digest.Digest{_path, norm, _dir, is_laws, _is_law_file, exempt, tops, says, _deps, _laws}:
      CoverageView{norm, is_laws, exempt, tops, says}

# coverage by reach (laws/LawNamesEveryItem.bend). A def is covered when a quantified law of
# a LAWS.bend names it, or when a covered def calls it: the least set of
# items that holds what the laws name and every call of each def in it. A
# type is covered when that set holds it or one of its constructors: a law or
# a covered def names it, and a type calls nothing. The set is stated over a
# graph written as digests, so the closure laws' spec of a closure (the least
# list that holds its start and is shut, unsafe.shut) is the same spec here:
# each node is a digest whose path is an item's key and whose imports are
# what the item leads to. An item's key is its name, a space and its file's
# path; one more node, the empty key, leads to what the laws name. A def
# leads to what the uses on its lines name (its calls, `Digest.Top`), in its
# file or behind an import alias; a type and a constructor lead nowhere.
# Every file's items are nodes, law files and tests too, so a helper of a
# LAWS.bend that a law names carries the reach to what it calls.

# an item's key: its name, a space, its file's path
def reach.key(+pp: String, name: String) -> String:
  name ++ " " ++ pp

# the keys of what the mentions name
def reach.keys(ms: List<&2, Digest.Mention>) -> List<&2, String>:
  match ms:
    case Nil{}:
      []
    case Con{Digest.Mention{pp, name}, rest}:
      reach.key(pp, name) <> reach.keys(rest)

# a node: a digest with only a key and what it leads to
def reach.node(+kk: String, to: List<&2, String>) -> Digest.Digest:
  Digest.Digest{kk, kk, "", False{}, False{}, True{}, [], [], to, []}

# each constructor as a node that leads nowhere, onto the others
def reach.ctors(cs: List<&2, String>, +pp: String, more: List<&2, Digest.Digest>) -> List<&2, Digest.Digest>:
  match cs:
    case Nil{}:
      more
    case Con{name, rest}:
      reach.node(reach.key(pp, name), []) <> reach.ctors(rest, pp, more)

# the defs and types of a file as nodes, onto the others: a def leads to
# what its calls name, a type (then each of its constructors) nowhere
def reach.nodes(ts: List<&2, Digest.Top>, +pp: String, more: List<&2, Digest.Digest>) -> List<&2, Digest.Digest>:
  match ts:
    case Nil{}:
      more
    case Con{Digest.Top{Outline.IDef{}, name, _line, _cs, calls}, rest}:
      reach.node(reach.key(pp, name), reach.keys(calls)) <> reach.nodes(rest, pp, more)
    case Con{Digest.Top{Outline.IType{}, name, _line, cs, _calls}, rest}:
      reach.node(reach.key(pp, name), []) <> reach.ctors(cs, pp, reach.nodes(rest, pp, more))
    case Con{_other, rest}:
      reach.nodes(rest, pp, more)

# the items of every file as nodes
def reach.items(ds: List<&2, Digest.Digest>) -> List<&2, Digest.Digest>:
  match ds:
    case Nil{}:
      []
    case Con{Digest.Digest{_path, norm, _dir, _is_laws, _is_law_file, _exempt, tops, _says, _deps, _laws},
      rest}:
      reach.nodes(tops, norm, reach.items(rest))

# what the quantified laws of every LAWS.bend name, in order
def reach.named(ds: List<&2, Digest.Digest>) -> List<&2, Digest.Mention>:
  match ds:
    case Nil{}:
      []
    case Con{Digest.Digest{_path, _norm, _dir, is_laws, _is_law_file, _exempt, _tops, says, _deps, _laws},
      rest}:
      +more = reach.named(rest)
      Bool.pick(List<&2, Digest.Mention>, is_laws, List.append(&2, Digest.Mention, says, more), more)

# the graph: the empty key, leading to what the laws name, then every item
def reach.graph(+ds: List<&2, Digest.Digest>) -> List<&2, Digest.Digest>:
  reach.node("", reach.keys(reach.named(ds))) <> reach.items(ds)

# what the laws reach: the closure of the empty key over the graph
def reach.closure(+ds: List<&2, Digest.Digest>) -> List<&2, String>:
  D1.unsafe.closure(reach.graph(ds), "")

# is one of the names (a type's constructors) of the file reached?
def reach.any(ns: List<&2, String>, +cl: List<&2, String>, +pp: String) -> Bool:
  match ns:
    case Nil{}:
      False{}
    case Con{name, rest}:
      Bool.or(Imports.has(cl, reach.key(pp, name)), reach.any(rest, cl, pp))

# the items of a file the closure does not hold, in order: a def whose name
# has no dot (a helper's has), and a type when neither it nor any of its
# constructors is held
def reach.gaps(ts: List<&2, Digest.Top>, +cl: List<&2, String>, +pp: String, +path: String) -> List<&2, F.Finding>:
  match ts:
    case Nil{}:
      []
    case Con{Digest.Top{Outline.IDef{}, +name, +line, _cs, _calls}, rest}:
      +more = reach.gaps(rest, cl, pp, path)
      Bool.pick(List<&2, F.Finding>, Bool.or(String.contains(name, "."), Imports.has(cl, reach.key(pp, name))), more,
        F.Finding{path, line, 0, 0, "coverage", "No quantified law reaches def " ++ name ++ "."} <> more)
    case Con{Digest.Top{Outline.IType{}, +name, +line, cs, _calls}, rest}:
      +more = reach.gaps(rest, cl, pp, path)
      Bool.pick(List<&2, F.Finding>, Bool.or(Imports.has(cl, reach.key(pp, name)), reach.any(cs, cl, pp)), more,
        F.Finding{path, line, 0, 0, "coverage",
            "No quantified law reaches type " ++ name ++ " or any of its constructors."}
          <> more)
    case Con{_other, rest}:
      reach.gaps(rest, cl, pp, path)

# the gaps of every file of fs that is not a law file or a test
def reach.files(fs: List<&2, Digest.Digest>, +cl: List<&2, String>) -> List<&2, F.Finding>:
  match fs:
    case Nil{}:
      []
    case Con{Digest.Digest{path, norm, _dir, _is_laws, _is_law_file, exempt, tops, _says, _deps, _laws},
      rest}:
      match exempt:
        case True{}:
          reach.files(rest, cl)
        case False{}:
          List.append(&2, F.Finding, reach.gaps(tops, cl, norm, path), reach.files(rest, cl))

# LAW: over every list of digests, coverage reports exactly this: when one
# is a LAWS.bend, in every file that is not a law file or a test, each def
# with no dot in its name, and each type, that the closure does not hold (a
# type by its key or a constructor's): the defs and types in scope less what
# the laws reach; else nothing
law coverage_reach:
  for +ds: List<&2, Digest.Digest>
  {Coverage.check(ds) == Bool.pick(List<&2, F.Finding>, coverage.lawful(ds), reach.files(ds, reach.closure(ds)), [])
    : List<&2, F.Finding>}

# LAW: over every list of digests, the closure holds the empty key it starts
# from
law reach_from:
  for +ds: List<&2, Digest.Digest>
  {Imports.has(reach.closure(ds), "") == True{} : Bool}

# LAW: over every list of digests, the closure is shut: each node of the
# graph that a node in it leads to is in it. So it holds every item a
# quantified law names, and every item a def in it calls
law reach_shut:
  for +ds: List<&2, Digest.Digest>
  {D1.unsafe.shut(reach.graph(ds), reach.closure(ds), reach.closure(ds)) == True{} : Bool}

# LAW: and it is the least such list: every list that holds the empty key
# and is shut holds each key the closure holds, so the closure holds only
# items a chain of calls from what a law names leads to
law reach_least:
  for +ds: List<&2, Digest.Digest>
  for +ss: List<&2, String>
  for +kk: String
  for hf: {Imports.has(ss, "") == True{} : Bool}
  for hs: {D1.unsafe.shut(reach.graph(ds), ss, ss) == True{} : Bool}
  for hk: {Imports.has(reach.closure(ds), kk) == True{} : Bool}
  {Imports.has(ss, kk) == True{} : Bool}

# the uses, in order, before the first one at or past the line
def reach.before(us: List<&2, Bind.Use>, +at: U32) -> List<&2, Bind.Use>:
  match us:
    case Nil{}:
      []
    case Con{Bind.Use{nm, +ln, cc, tt}, rest}:
      Bool.pick(List<&2, Bind.Use>, U32.is_le(at, ln), [], Bind.Use{nm, ln, cc, tt} <> reach.before(rest, at))

# the uses from the first one at or past the line on
def reach.after(us: List<&2, Bind.Use>, +at: U32) -> List<&2, Bind.Use>:
  match us:
    case Nil{}:
      []
    case Con{Bind.Use{nm, +ln, cc, tt}, +rest}:
      Bool.pick(List<&2, Bind.Use>, U32.is_le(at, ln), Bind.Use{nm, ln, cc, tt} <> rest, reach.after(rest, at))

# the line of the next item that is not a constructor, when there is one
def reach.next(items: List<&2, Outline.Item>) -> Maybe<&2, U32>:
  match items:
    case Nil{}:
      None{}
    case Con{Outline.Item{Outline.ICtor{}, _name, _line, _sig, _doc, _path}, rest}:
      reach.next(rest)
    case Con{Outline.Item{_kind, _name, line, _sig, _doc, _path}, _rest}:
      Some{line}

# the uses an item takes: those before the next item's line, or all of them
def reach.upto(us: List<&2, Bind.Use>, mm: Maybe<&2, U32>) -> List<&2, Bind.Use>:
  match mm:
    case None{}:
      us
    case Some{at}:
      reach.before(us, at)

# the uses an item leaves to the items after it
def reach.past(us: List<&2, Bind.Use>, mm: Maybe<&2, U32>) -> List<&2, Bind.Use>:
  match mm:
    case None{}:
      []
    case Some{at}:
      reach.after(us, at)

# what the uses name, in order, resolved against the file's outline
def reach.calls(us: List<&2, Bind.Use>, +all: List<&2, Outline.Item>, +file: String) -> List<&2, Digest.Mention>:
  match us:
    case Nil{}:
      []
    case Con{Bind.Use{_n, _l, _c, tt}, rest}:
      List.append(&2, Digest.Mention, coverage.target(tt, all, file), reach.calls(rest, all, file))

# a def's name onto the others, when it has one and is a proof
def reach.proof(mm: Maybe<&2, String>, is_proof: Bool, +more: List<&2, String>) -> List<&2, String>:
  match mm:
    case None{}:
      more
    case Some{name}:
      Bool.pick(List<&2, String>, is_proof, name <> more, more)

# the names of the tree's top-level defs that are proofs, as
# laws/ExemptPathsYieldNoFindings.bend reads one (Calls.proof) off its whole
# header, wrapped or not (laws/DefSignatureRunsToItsColon.bend), in order
def reach.proofs(root: Tree.Node) -> List<&2, String>:
  match root:
    case Tree.NCons{Tree.Stmt{Tree.SDef{}, +kids, body}, rest}:
      reach.proof(Bind.declared(kids), Calls.proof(Calls.header(kids, body)), reach.proofs(rest))
    case Tree.NCons{_h, rest}:
      reach.proofs(rest)
    case _other:
      []

# the defs and types of the outline, less the defs named in ps (the
# proofs), each by name and line, a type with its constructors, each with
# what the uses on its lines name. The uses are read in order: each item but
# a constructor takes those before the next such item's line, a proof's
# included
def reach.tops(
  items: List<&2, Outline.Item>,
  +all: List<&2, Outline.Item>,
  +us: List<&2, Bind.Use>,
  +file: String,
  +ps: List<&2, String>
) -> List<&2, Digest.Top>:
  match items:
    case Nil{}:
      []
    case Con{Outline.Item{Outline.IDef{}, +name, line, _sig, _doc, _path}, +rest}:
      Bool.pick(List<&2, Digest.Top>, Imports.has(ps, name),
        reach.tops(rest, all, reach.past(us, reach.next(rest)), file, ps),
        Digest.Top{Outline.IDef{}, name, line, [], reach.calls(reach.upto(us, reach.next(rest)), all, file)}
          <> reach.tops(rest, all, reach.past(us, reach.next(rest)), file, ps))
    case Con{Outline.Item{Outline.IType{}, name, line, _sig, _doc, _path}, +rest}:
      Digest.Top{Outline.IType{}, name, line, coverage.ctors_of(rest),
        reach.calls(reach.upto(us, reach.next(rest)), all, file)}
        <> reach.tops(rest, all, reach.past(us, reach.next(rest)), file, ps)
    case Con{Outline.Item{Outline.ICtor{}, _name, _line, _sig, _doc, _path}, rest}:
      reach.tops(rest, all, us, file, ps)
    case Con{Outline.Item{_kind, _name, _line, _sig, _doc, _path}, +rest}:
      reach.tops(rest, all, reach.past(us, reach.next(rest)), file, ps)

# LAW: whatever a file's text, tokens, tree, binding structure and outline,
# its digest grades it at its normalized path, is a LAWS.bend by its path, is
# let off exactly when that path is a law file or a test, lists the outline's
# defs and types (a type with the constructors listed right after it) less
# the defs that are proofs (reach.proofs of its tree), each
# with what the binder resolved the uses on its lines to (reach.tops), and
# names, when it is a LAWS.bend, exactly what the binder resolved each use on
# a quantified law's statement to, through an import alias or in the file;
# any other file names nothing
law reach_digest:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for +tree: Tree.Node
  for +bound: Bind.Bound
  for +items: List<&2, Outline.Item>
  {coverage.view(Digest.of(Src.Src{path, text, toks, tree, bound, items}))
    == CoverageView{Imports.norm(path), Paths.is_laws(path),
      Bool.or(Paths.is_law_file(Imports.norm(path)), Paths.is_test(Imports.norm(path))),
      reach.tops(items, items, coverage.uses(bound), Imports.norm(path), reach.proofs(tree)),
      Bool.pick(List<&2, Digest.Mention>, Paths.is_laws(path),
        coverage.said(coverage.uses(bound), tree, items, Imports.norm(path)), [])}
    : CoverageView}

# LAW: the linter does not read a file's role off its path: it tells the
# digest the role the file has among the files of the run (src/role.bend).
# That digest, whatever the role and whatever the file's text, tokens, tree,
# binding structure and outline, holds the path as given, the normalized path
# it is graded at and its directory; is a LAWS.bend exactly when the role is
# a law file's and a law or proof file exactly when the role says so; is let
# off exactly when the role is a law or proof file's or the normalized path
# is a test; lists the outline's defs and types less the defs that are
# proofs, each with what the binder resolved the uses on its lines to
# (reach.tops, as reach_digest reads them); names what the quantified laws'
# statements name exactly when the role is a law file's; and holds the files
# the outline imports and, for a law file's role, the tree's laws. No field
# is left to the code alone
law reach_digest_role:
  for +rr: Role.Role
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for +tree: Tree.Node
  for +bound: Bind.Bound
  for +items: List<&2, Outline.Item>
  {Digest.of.role(rr, Src.Src{path, text, toks, tree, bound, items})
    == Digest.Digest{path, Imports.norm(path), Imports.dir_of(path), Role.is_laws(rr), Role.is_law_file(rr),
      Bool.or(Role.is_law_file(rr), Paths.is_test(Imports.norm(path))),
      reach.tops(items, items, coverage.uses(bound), Imports.norm(path), reach.proofs(tree)),
      Bool.pick(List<&2, Digest.Mention>, Role.is_laws(rr),
        coverage.said(coverage.uses(bound), tree, items, Imports.norm(path)), []),
      Imports.targets(items, Imports.norm(path)), Digest.laws.in(Role.is_laws(rr), tree, items)}
    : Digest.Digest}

# LAW: over the files of a run, each file's digest is told the role the
# run's marks give its path (Role.of), file by file, in order
law reach_digest_marks:
  for +ms: List<&2, Role.Mark>
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  for ss: List<&2, Src.Src>
  {Digest.all.role(ms, Src.Src{path, text, toks, tree, bound, items} <> ss)
    == Digest.of.role(Role.of(ms, path), Src.Src{path, text, toks, tree, bound, items}) <> Digest.all.role(ms, ss)
    : List<&2, Digest.Digest>}

# LAW: read from its path and text as the linter reads every file, a file's
# defs call, and its laws name, exactly what the binder (Bind.of_tree,
# laws/BinderResolvesInnermostFirst.bend) resolves each use to: on the def's lines, and on a quantified
# law's statement when the file is a LAWS.bend; a def that is a proof is not
# listed
law reach_binder:
  for +path: String
  for +text: String
  {coverage.view(Digest.of(Src.of(path, text)))
    == CoverageView{Imports.norm(path), Paths.is_laws(path),
      Bool.or(Paths.is_law_file(Imports.norm(path)), Paths.is_test(Imports.norm(path))),
      reach.tops(Outline.of_tokens(text, Lex.tokens(text)), Outline.of_tokens(text, Lex.tokens(text)),
        coverage.uses(Bind.of_tree(Tree.parse(text), String.lines(text))), Imports.norm(path),
        reach.proofs(Tree.parse(text))),
      Bool.pick(List<&2, Digest.Mention>, Paths.is_laws(path),
        coverage.said(coverage.uses(Bind.of_tree(Tree.parse(text), String.lines(text))), Tree.parse(text),
          Outline.of_tokens(text, Lex.tokens(text)), Imports.norm(path)), [])}
    : CoverageView}

# LAW: a law's doc is looked for from the first item at or after its line: an
# item sits there when the line is at or before the item's own
law from_line_stops_at_item:
  for kk: Outline.ItemKind
  for nn: String
  for +ln: U32
  for sig: String
  for doc: String
  for pp: String
  for rest: List<&2, Outline.Item>
  for +at: U32
  {Digest.from_line.stop(Outline.Item{kk, nn, ln, sig, doc, pp} <> rest, at) == U32.is_le(at, ln) : Bool}

# LAW: with no item left, the search stops
law from_line_stops_at_end:
  for items: List<&2, Outline.Item>
  for +at: U32
  for e: {List.is_empty(&2, Outline.Item, items) == True{} : Bool}
  {Digest.from_line.stop(items, at) == True{} : Bool}

# LAW: every law statement of a tree is one of its laws, in order: its
# declared name, its line, whether its body binds, and the doc of the item
# on its line, the items searched on from where the last law's search stopped
law laws_of_takes_each_law:
  for +kids: Tree.Node
  for body: Tree.Node
  for rest: Tree.Node
  for +items: List<&2, Outline.Item>
  {Digest.laws_of(Tree.NCons{Tree.Stmt{Tree.SLaw{}, kids, body}, rest}, items)
    == Digest.Law{Closed.name.of(Bind.declared(kids)), Tree.line(kids), Closed.binds(body),
      String.lines(Digest.doc_at(
        Digest.from_line(items, Tree.line(kids), Digest.from_line.stop(items, Tree.line(kids))), Tree.line(kids)))}
      <> Digest.laws_of(rest,
        Digest.from_line(items, Tree.line(kids), Digest.from_line.stop(items, Tree.line(kids))))
    : List<&2, Digest.Law>}
