# src/role: what a file of the run is to the laws -- a law file, a proof
# file, or neither. A LAWS.bend is a law file and a PROOF.bend a proof file,
# by name, as Bend reads them. Any other file is on the laws' side when a
# LAWS.bend or a PROOF.bend reaches it by relative imports and the code does
# not: the code is every package's main.bend and every file the laws do not
# reach, and all they import. On the laws' side, a file a LAWS.bend reaches is
# a law file and any other a proof file, one only a PROOF.bend reaches, so a
# proof may state laws of its own. So `LAWS.bend` can be nothing but
# `import ./laws/x.bend as X` lines, the files it reaches are held to what a
# law file is held to, and the code they state laws about, which main.bend
# imports, is still code.
#
# A file needs no LAWS.bend above it to be on the laws' side: what it holds
# says so too (`own`). A file that fills a law (a def that is a proof: it
# returns one, or is written with no type) is a proof file, and one that
# states a law and fills none a law file, unless it is a package's
# main.bend, which is code whatever it holds; a file that imports a law file
# of the run is on the laws' side as well (a proof made of imports alone).
# So one guarantee per file under laws/ and proofs/ is read right with no
# root file, and over the whole tree the code still wins: a file the code
# imports is code, laws and all. Over files named on the line the walk does
# not run, since the code that imports a file may not be in the run: each
# file has its own role (src/lint/plan.bend). Pure.
import Base
import ./paths.bend as Paths
import ./src.bend as Src
import ./lazy/lazy.bend as Lazy
import ./syntax/tree.bend as Tree
import ./rules/imports.bend as Imports
import ./rules/calls.bend as Calls
import ./syntax/outline.bend as Outline
import ./finding.bend as F

# what a file is to the laws
type Role is Data:
  Plain{}
  Laws{}
  Proof{}

# a file's role by its name alone: a LAWS.bend, a PROOF.bend, or neither
def of_path(+path: String) -> Role:
  Bool.pick(Role, Paths.is_laws(path), Laws{}, Bool.pick(Role, Paths.is_proof(path), Proof{}, Plain{}))

# is it a law file?
def is_laws(rr: Role) -> Bool:
  match rr:
    case Laws{}:
      True{}
    case other:
      False{}

# is it a proof file?
def is_proof(rr: Role) -> Bool:
  match rr:
    case Proof{}:
      True{}
    case other:
      False{}

# is it a law file or a proof file?
def is_law_file(rr: Role) -> Bool:
  match rr:
    case Plain{}:
      False{}
    case other:
      True{}

# a rule that has nothing to say of a law or proof file: its findings on a
# file told its role, none on one of those
def skip(+rr: Role, run: Unit -> List<&2, F.Finding>) -> List<&2, F.Finding>:
  Lazy.stop(List<&2, F.Finding>, is_law_file(rr), [], run)

# reading a file
# --------------

# is the item a law?
def law_item(kk: Outline.ItemKind) -> Bool:
  match kk:
    case Outline.ILaw{}:
      True{}
    case other:
      False{}

# does the outline state a law? hit: the item before did
def states.go(its: List<&2, Outline.Item>, hit: Bool) -> Bool:
  match its:
    case Nil{}:
      hit
    case Con{Outline.Item{k, _name, _line, _sig, _doc, _path}, rest}:
      match hit:
        case True{}:
          True{}
        case False{}:
          states.go(rest, law_item(k))

# does the outline state a law?
def states(its: List<&2, Outline.Item>) -> Bool:
  states.go(its, False{})

# does one of the defs fill a law (Calls.proof)? hit: the def before did
def fills.go(ds: List<&2, Calls.Def>, hit: Bool) -> Bool:
  match ds:
    case Nil{}:
      hit
    case Con{Calls.Def{_name, +sig, _body}, rest}:
      match hit:
        case True{}:
          True{}
        case False{}:
          fills.go(rest, Calls.proof(sig))

# does a def of the tree fill a law?
def fills(tree: Tree.Node) -> Bool:
  fills.go(Calls.defs(tree), False{})

# a file's role by itself: a LAWS.bend or PROOF.bend by its name; else, but
# for a package's main.bend (entry), a proof file when it fills a law and a
# law file when it states one; else neither
def own.of(+named: Role, entry: Bool, fills: Bool, states: Bool) -> Role:
  Bool.pick(Role, is_law_file(named), named,
    Bool.pick(Role, entry, Plain{}, Bool.pick(Role, fills, Proof{}, Bool.pick(Role, states, Laws{}, Plain{}))))

# a parsed file's role by itself (own.of)
def own(ss: Src.Src) -> Role:
  Src.Src{+path, _text, _toks, tree, _bound, items} = ss
  own.of(of_path(path), String.eq(Paths.base(path), "main.bend"), fills(tree), states(items))

# what a file on the laws' side is: a law file when a LAWS.bend reaches it,
# else a proof file
def reached(laws: Bool) -> Role:
  Bool.pick(Role, laws, Laws{}, Proof{})

# one file as the walk reads it: its normalized path, what it imports, its
# own role (by name, else by what it holds), and whether it is a package's
# entry (a main.bend)
type Fact is Data:
  Fact{norm: String, deps: List<&2, String>, named: Role, entry: Bool}

# a parsed file read down to its fact
def fact(ss: Src.Src) -> Fact:
  Src.Src{+path, text, toks, tree, bound, +items} = ss
  +nn = Imports.norm(path)
  Fact{nn, Imports.targets(items, nn), own(Src.Src{path, text, toks, tree, bound, items}),
    String.eq(Paths.base(path), "main.bend")}

# every file's fact, in order
def facts(ss: List<&2, Src.Src>) -> List<&2, Fact>:
  match ss:
    case Nil{}:
      Nil{}
    case Con{s, rest}:
      fact(s) <> facts(rest)

# the walks
# ---------

# a file (normalized) and its role
type Mark is Data:
  Mark{norm: String, role: Role}

# the import graph of the files
def edges(fs: List<&2, Fact>) -> List<&2, Imports.Edge>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{Fact{norm, deps, _named, _entry}, rest}:
      Imports.Edge{norm, deps} <> edges(rest)

# the paths of the files
def paths(fs: List<&2, Fact>) -> List<&2, String>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{Fact{norm, _deps, _named, _entry}, rest}:
      norm <> paths(rest)

# the roots of the laws: every file that is a law or proof file by itself
def roots(fs: List<&2, Fact>) -> List<&2, String>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{Fact{norm, _deps, +named, _entry}, rest}:
      +more = roots(rest)
      Bool.pick(List<&2, String>, is_law_file(named), norm <> more, more)

# the roots of the law files: every file that is a law file by itself
def lawful(fs: List<&2, Fact>) -> List<&2, String>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{Fact{norm, _deps, +named, _entry}, rest}:
      +more = lawful(rest)
      Bool.pick(List<&2, String>, is_laws(named), norm <> more, more)

# do the imports hold one of the paths? Over the paths first, so none to
# look for answers at once; hit: the path before was held
def imports.any(ls: List<&2, String>, +deps: List<&2, String>, hit: Bool) -> Bool:
  match ls:
    case Nil{}:
      hit
    case Con{l, rest}:
      match hit:
        case True{}:
          True{}
        case False{}:
          imports.any(rest, deps, Imports.has(deps, l))

# the files no role of their own puts on the laws' side that import a law
# file of the run (lawful): a proof made of imports alone
def feeds(fs: List<&2, Fact>, +lawful: List<&2, String>) -> List<&2, String>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{Fact{norm, +deps, +named, _entry}, rest}:
      +more = feeds(rest, lawful)
      +hit = Bool.and(Bool.not(is_law_file(named)), imports.any(lawful, deps, False{}))
      Bool.pick(List<&2, String>, hit, norm <> more, more)

# what the walk from some files reaches, through every file of the run
def reach(+fs: List<&2, Fact>, +from: List<&2, String>) -> List<&2, String>:
  Imports.walk(List.length(&2, Fact, fs), from, from, edges(fs), paths(fs))

# the roots of the code: every package's main.bend, and every file the laws
# do not reach
def code(fs: List<&2, Fact>, +laws: List<&2, String>) -> List<&2, String>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{Fact{+norm, _deps, _named, entry}, rest}:
      +more = code(rest, laws)
      Bool.pick(List<&2, String>, Bool.or(entry, Bool.not(Imports.has(laws, norm))), norm <> more, more)

# a file's role: its role by name, or else its role on the laws' side
def role.of(+named: Role, reach: Role) -> Role:
  Bool.pick(Role, is_law_file(named), named, reach)

# the marks of the files the laws reach and the code does not, in the run's
# order: a law file when a LAWS.bend reaches it
def marks.of(
  fs: List<&2, Fact>,
  +laws: List<&2, String>,
  +lawful: List<&2, String>,
  +code: List<&2, String>
) -> List<&2, Mark>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{Fact{+norm, _deps, +named, _entry}, rest}:
      +more = marks.of(rest, laws, lawful, code)
      Bool.pick(List<&2, Mark>, Bool.and(Imports.has(laws, norm), Bool.not(Imports.has(code, norm))),
        Mark{norm, role.of(named, reached(Imports.has(lawful, norm)))} <> more, more)

# the role of every file on the laws' side. Both walks are the one every
# project rule takes over imports (src/rules/imports.bend), each from all its
# roots at once
def marks(ss: List<&2, Src.Src>) -> List<&2, Mark>:
  +fs = facts(ss)
  +lw = lawful(fs)
  +ls = reach(fs, List.append(&2, String, roots(fs), feeds(fs, lw)))
  marks.of(fs, ls, reach(fs, lw), reach(fs, code(fs, ls)))

# a normalized path's role among the marks: neither when it is not marked
def of.norm(ms: List<&2, Mark>, +nn: String) -> Role:
  match ms:
    case Nil{}:
      Plain{}
    case Con{Mark{+norm, role}, rest}:
      Lazy.either(Role, String.eq(norm, nn), _u => role, _v => of.norm(rest, nn))

# a file's role among the marks: a LAWS.bend or PROOF.bend by its name, any
# other file as marked, and neither when it is not marked
def of(ms: List<&2, Mark>, +path: String) -> Role:
  role.of(of_path(path), of.norm(ms, Imports.norm(path)))
