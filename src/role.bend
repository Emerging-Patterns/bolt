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
# imports, is still code. Pure.
import Base
import ./paths.bend as Paths
import ./src.bend as Src
import ./lazy/lazy.bend as Lazy
import ./rules/imports.bend as Imports
import ./syntax/lex.bend as Lex
import ./syntax/outline.bend as Outline
import ./finding.bend as F
import ./syntax/bind.bend as Bind

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

# what a file on the laws' side is: a law file when a LAWS.bend reaches it,
# else a proof file
def reached(laws: Bool) -> Role:
  Bool.pick(Role, laws, Laws{}, Proof{})

# one file as the walk reads it: its normalized path, what it imports, its
# role by name, and whether it is a package's entry (a main.bend)
type Fact is Data:
  Fact{norm: String, deps: List<&2, String>, named: Role, entry: Bool}

# a parsed file read down to its fact
def fact(ss: Src.Src) -> Fact:
  Src.Src{+path, _text, _toks, _tree, _bound, items} = ss
  +nn = Imports.norm(path)
  Fact{nn, Imports.targets(items, nn), of_path(path), String.eq(Paths.base(path), "main.bend")}

# a file's fact read from its text alone: lexed and outlined for its imports,
# never parsed, so a file read only for its place in the graph costs little
def fact.text(+path: String, +text: String) -> Fact:
  +nn = Imports.norm(path)
  Fact{nn, Imports.targets(Outline.of_tokens(text, Lex.tokens(text)), nn), of_path(path),
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

# the roots of the laws: every LAWS.bend and PROOF.bend
def roots(fs: List<&2, Fact>) -> List<&2, String>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{Fact{norm, _deps, +named, _entry}, rest}:
      +more = roots(rest)
      Bool.pick(List<&2, String>, is_law_file(named), norm <> more, more)

# the roots of the law files: every LAWS.bend
def lawful(fs: List<&2, Fact>) -> List<&2, String>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{Fact{norm, _deps, +named, _entry}, rest}:
      +more = lawful(rest)
      Bool.pick(List<&2, String>, is_laws(named), norm <> more, more)

# what the walk from some files reaches, through every file of the run
def reach(+fs: List<&2, Fact>, +from: List<&2, String>) -> List<&2, String>:
  Imports.walk(List.length(&2, Fact, fs), from, from, edges(fs), paths(fs))

def code.fast(fs: List<&2, Fact>, +lx: Bind.Index) -> List<&2, String>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{Fact{+norm, _deps, _named, entry}, rest}:
      +more = code.fast(rest, lx)
      Bool.pick(List<&2, String>, Bool.or(entry, Bool.not(Bind.indexed(lx, norm))), norm <> more, more)

# the roots of the code: every package's main.bend, and every file the laws
# do not reach. Each file asks the binder's index (src/syntax/bind.bend) of
# what the laws reach: a scan of that list for every file is the files
# squared
def code(fs: List<&2, Fact>, +laws: List<&2, String>) -> List<&2, String>:
  code.fast(fs, Bind.index(laws))

# a file's role: its role by name, or else its role on the laws' side
def role.of(+named: Role, reach: Role) -> Role:
  Bool.pick(Role, is_law_file(named), named, reach)

def marks.fast(fs: List<&2, Fact>, +lx: Bind.Index, +fx: Bind.Index, +cx: Bind.Index) -> List<&2, Mark>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{Fact{+norm, _deps, +named, _entry}, rest}:
      +more = marks.fast(rest, lx, fx, cx)
      Bool.pick(List<&2, Mark>, Bool.and(Bind.indexed(lx, norm), Bool.not(Bind.indexed(cx, norm))),
        Mark{norm, role.of(named, reached(Bind.indexed(fx, norm)))} <> more, more)

# the marks of the files the laws reach and the code does not, in the run's
# order: a law file when a LAWS.bend reaches it. What each walk reaches is
# put in the binder's index once, and each file asks the three indexes,
# where three scans for every file were the files squared (1.7 s of the 5 s
# the marks took on a project of 4,062 files)
def marks.of(
  fs: List<&2, Fact>,
  +laws: List<&2, String>,
  +lawful: List<&2, String>,
  +code: List<&2, String>
) -> List<&2, Mark>:
  marks.fast(fs, Bind.index(laws), Bind.index(lawful), Bind.index(code))

# the role of every file on the laws' side of a graph given as facts
def marks.facts(+fs: List<&2, Fact>) -> List<&2, Mark>:
  +ls = reach(fs, roots(fs))
  marks.of(fs, ls, reach(fs, lawful(fs)), reach(fs, code(fs, ls)))

# the role of every file on the laws' side. Both walks are the one every
# project rule takes over imports (src/rules/imports.bend), each from all its
# roots at once
def marks(ss: List<&2, Src.Src>) -> List<&2, Mark>:
  marks.facts(facts(ss))


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
