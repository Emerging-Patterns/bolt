# src/role: what a file of the run is to the laws -- a law file, a proof
# file, or neither. A LAWS.bend is a law file and a PROOF.bend a proof file,
# by name, as Bend reads them. Any other file is on the laws' side when a
# LAWS.bend or a PROOF.bend reaches it by relative imports and the code does
# not: the code is every package's main.bend and every file the laws do not
# reach, and all they import. On the laws' side, a file that declares a law
# is a law file and any other a proof file. So `LAWS.bend` can be nothing but
# `import ./laws/x.bend as X` lines, the files it reaches are held to what a
# law file is held to, and the code they state laws about, which main.bend
# imports, is still code. Pure.
import Base
import ./paths.bend as Paths
import ./src.bend as Src
import ./lazy/lazy.bend as Lazy
import ./syntax/tree.bend as Tree
import ./rules/imports.bend as Imports
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

# does the file declare a law?
def declares(root: Tree.Node) -> Bool:
  match root:
    case Tree.NCons{Tree.Stmt{Tree.SLaw{}, _kids, _body}, _rest}:
      True{}
    case Tree.NCons{_h, rest}:
      declares(rest)
    case other:
      False{}

# what a file on the laws' side is: a law file when it declares a law, else a
# proof file
def reached(laws: Bool) -> Role:
  Bool.pick(Role, laws, Laws{}, Proof{})

# one file as the walk reads it: its normalized path, what it imports, its
# role by name, its role on the laws' side, and whether it is a package's
# entry (a main.bend)
type Fact is Data:
  Fact{norm: String, deps: List<&2, String>, named: Role, reach: Role, entry: Bool}

# a parsed file read down to its fact
def fact(ss: Src.Src) -> Fact:
  Src.Src{+path, _text, _toks, tree, _bound, items} = ss
  +nn = Imports.norm(path)
  Fact{nn, Imports.targets(items, nn), of_path(path), reached(declares(tree)), String.eq(Paths.base(path), "main.bend")}

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
    case Con{Fact{norm, deps, _named, _reach, _entry}, rest}:
      Imports.Edge{norm, deps} <> edges(rest)

# the paths of the files
def paths(fs: List<&2, Fact>) -> List<&2, String>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{Fact{norm, _deps, _named, _reach, _entry}, rest}:
      norm <> paths(rest)

# the roots of the laws: every LAWS.bend and PROOF.bend
def roots(fs: List<&2, Fact>) -> List<&2, String>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{Fact{norm, _deps, +named, _reach, _entry}, rest}:
      +more = roots(rest)
      Bool.pick(List<&2, String>, is_law_file(named), norm <> more, more)

# what the walk from some files reaches, through every file of the run
def reach(+fs: List<&2, Fact>, +from: List<&2, String>) -> List<&2, String>:
  Imports.walk(List.length(&2, Fact, fs), from, from, edges(fs), paths(fs))

# the roots of the code: every package's main.bend, and every file the laws
# do not reach
def code(fs: List<&2, Fact>, +laws: List<&2, String>) -> List<&2, String>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{Fact{+norm, _deps, _named, _reach, entry}, rest}:
      +more = code(rest, laws)
      Bool.pick(List<&2, String>, Bool.or(entry, Bool.not(Imports.has(laws, norm))), norm <> more, more)

# a file's role: its role by name, or else its role on the laws' side
def role.of(+named: Role, reach: Role) -> Role:
  Bool.pick(Role, is_law_file(named), named, reach)

# the marks of the files the laws reach and the code does not, in the run's
# order
def marks.of(fs: List<&2, Fact>, +laws: List<&2, String>, +code: List<&2, String>) -> List<&2, Mark>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{Fact{+norm, _deps, +named, reach, _entry}, rest}:
      +more = marks.of(rest, laws, code)
      Bool.pick(List<&2, Mark>, Bool.and(Imports.has(laws, norm), Bool.not(Imports.has(code, norm))),
        Mark{norm, role.of(named, reach)} <> more, more)

# the role of every file on the laws' side. Both walks are the one every
# project rule takes over imports (src/rules/imports.bend), each from all its
# roots at once
def marks(ss: List<&2, Src.Src>) -> List<&2, Mark>:
  +fs = facts(ss)
  +ls = reach(fs, roots(fs))
  marks.of(fs, ls, reach(fs, code(fs, ls)))

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
