# A file's role in a run follows the imports, as src/role.bend's header says.
# The run reads each file down to a fact: its normalized path, what it
# imports, its role by name (a LAWS.bend, a PROOF.bend, or neither) and
# whether it is a package's entry, a main.bend. Three walks go over the
# imports, each through every file of the run (Imports.walk, which
# laws/ImportReachIsClosed.bend describes): from every LAWS.bend and
# PROOF.bend, what the laws reach; from every LAWS.bend, what the law files
# reach; and from the code's roots, every entry and every file the laws do
# not reach. A file is marked when the laws reach it and the code does not.
# Its role is then its role by name when it has one, and else a law file's
# exactly when a LAWS.bend reaches it, a proof file's otherwise. A path's
# role among the marks is the first mark's at that path, and neither when it
# has none; a LAWS.bend or a PROOF.bend keeps its role by name whatever the
# marks say.
import Base
import ../src/src.bend as Src
import ../src/paths.bend as Paths
import ../src/role.bend as Role
import ../src/rules/imports.bend as Imports
import ../src/syntax/lex.bend as Lex
import ../src/syntax/tree.bend as Tree
import ../src/syntax/bind.bend as Bind
import ../src/syntax/outline.bend as Outline

# Law vocabulary, down to the LAWs: bolt never calls any of it.

# each file with what it imports
def role.edges(fs: List<&2, Role.Fact>) -> List<&2, Imports.Edge>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{Role.Fact{norm, deps, _named, _entry}, rest}:
      Imports.Edge{norm, deps} <> role.edges(rest)

# each file's normalized path
def role.paths(fs: List<&2, Role.Fact>) -> List<&2, String>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{Role.Fact{norm, _deps, _named, _entry}, rest}:
      norm <> role.paths(rest)

# the files that are a LAWS.bend or a PROOF.bend by name
def role.roots(fs: List<&2, Role.Fact>) -> List<&2, String>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{Role.Fact{norm, _deps, +named, _entry}, rest}:
      +more = role.roots(rest)
      Bool.pick(List<&2, String>, Role.is_law_file(named), norm <> more, more)

# the files that are a LAWS.bend by name
def role.lawful(fs: List<&2, Role.Fact>) -> List<&2, String>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{Role.Fact{norm, _deps, +named, _entry}, rest}:
      +more = role.lawful(rest)
      Bool.pick(List<&2, String>, Role.is_laws(named), norm <> more, more)

# the code's roots: every entry, and every file not among those the laws reach
def role.code(fs: List<&2, Role.Fact>, +laws: List<&2, String>) -> List<&2, String>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{Role.Fact{+norm, _deps, _named, entry}, rest}:
      +more = role.code(rest, laws)
      Bool.pick(List<&2, String>, Bool.or(entry, Bool.not(List.contains(~String, ~String.eq, laws, norm))),
        norm <> more, more)

# a marked file's role: its role by name when it has one, else a law file's
# when a LAWS.bend reaches it and a proof file's when none does
def role.given(+named: Role.Role, lawful: Bool) -> Role.Role:
  Bool.pick(Role.Role, Role.is_law_file(named), named, Bool.pick(Role.Role, lawful, Role.Laws{}, Role.Proof{}))

# the marks of the files, in order, given what the laws reach, what the
# LAWS.bend files reach and what the code reaches: a file is marked exactly
# when the laws reach it and the code does not
def role.marks(
  fs: List<&2, Role.Fact>,
  +laws: List<&2, String>,
  +lawful: List<&2, String>,
  +code: List<&2, String>
) -> List<&2, Role.Mark>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{Role.Fact{+norm, _deps, +named, _entry}, rest}:
      +more = role.marks(rest, laws, lawful, code)
      Bool.pick(List<&2, Role.Mark>,
        Bool.and(List.contains(~String, ~String.eq, laws, norm),
          Bool.not(List.contains(~String, ~String.eq, code, norm))),
        Role.Mark{norm, role.given(named, List.contains(~String, ~String.eq, lawful, norm))} <> more, more)

# the role of the first mark at a path; neither when no mark is at it
def role.first(ms: List<&2, Role.Mark>, +n: String) -> Role.Role:
  match ms:
    case Nil{}:
      Role.Plain{}
    case Con{Role.Mark{+norm, role}, rest}:
      +more = role.first(rest, n)
      Bool.pick(Role.Role, String.eq(norm, n), role, more)

# LAW: a parsed file is read down to its normalized path, the relative
# imports of its outline resolved against that path, its role by name, and
# whether its last segment is main.bend
law fact_reads:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {Role.fact(Src.Src{path, text, toks, tree, bound, items})
    == Role.Fact{Imports.norm(path), Imports.targets(items, Imports.norm(path)), Role.of_path(path),
      String.eq(Paths.base(path), "main.bend")} : Role.Fact}

# LAW: a file read for its place in the graph alone, from its path and text
# and never parsed, gives the fact the parsed file gives
law fact_of_text:
  for +path: String
  for +text: String
  {Role.fact.text(path, text) == Role.fact(Src.of(path, text)) : Role.Fact}

# LAW: the files of a run are read down to their facts one by one, in order
law facts_in_order:
  for s: Src.Src
  for ss: List<&2, Src.Src>
  {Role.facts(s <> ss) == Role.fact(s) <> Role.facts(ss) : List<&2, Role.Fact>}

# LAW: what a walk from some files reaches is Imports.walk from all of them
# at once, each already seen, over every file's imports, with fuel for every
# file
law reach_walks:
  for +fs: List<&2, Role.Fact>
  for +from: List<&2, String>
  {Role.reach(fs, from)
    == Imports.walk(List.length(&2, Role.Fact, fs), from, from, role.edges(fs), role.paths(fs))
    : List<&2, String>}

# LAW: the marks of any files are those of the files the laws reach and the
# code does not, each with the role its name and the LAWS.bend files' reach
# give it, in the files' order: the laws' walk starts from every LAWS.bend and
# PROOF.bend, the law files' from every LAWS.bend, and the code's from every
# entry and every file the laws' walk does not reach
law marks_follow_imports:
  for +fs: List<&2, Role.Fact>
  {Role.marks.facts(fs)
    == role.marks(fs, Role.reach(fs, role.roots(fs)), Role.reach(fs, role.lawful(fs)),
      Role.reach(fs, role.code(fs, Role.reach(fs, role.roots(fs))))) : List<&2, Role.Mark>}

# LAW: the marks of a run are the marks of its files' facts
law marks_of_run:
  for s: List<&2, Src.Src>
  {Role.marks(s) == Role.marks.facts(Role.facts(s)) : List<&2, Role.Mark>}

# LAW: a normalized path's role among any marks is the first mark's at that
# path, and neither when no mark is at it
law role_of_first_mark:
  for ms: List<&2, Role.Mark>
  for +n: String
  {Role.of.norm(ms, n) == role.first(ms, n) : Role.Role}

# LAW: a file's role among any marks is its role by name when it is a
# LAWS.bend or a PROOF.bend, and else the first mark's at its normalized path
law role_of_path:
  for ms: List<&2, Role.Mark>
  for +path: String
  {Role.of(ms, path)
    == Bool.pick(Role.Role, Role.is_law_file(Role.of_path(path)), Role.of_path(path),
      role.first(ms, Imports.norm(path))) : Role.Role}
