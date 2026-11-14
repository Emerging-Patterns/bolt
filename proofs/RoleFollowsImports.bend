# proofs of laws/RoleFollowsImports.bend
import Base
import ../src/src.bend as Src
import ../src/paths.bend as Paths
import ../src/role.bend as Role
import ../src/lazy/lazy.bend as Lazy
import ../src/rules/imports.bend as Imports
import ../laws/RoleFollowsImports.bend as Laws
import ../src/syntax/bind.bend as Bind
import ./lemmas/BinderIndexIsContains.bend as M1

# roles from the imports (laws/RoleFollowsImports.bend). The law's
# vocabulary reads the facts the way src/role.bend does, so each list is the
# rule's by induction on the facts, and the marks are then the rule's marks
# over the same three walks.

# the graph of the facts is the law's
law rf.edges:
  for fs: List<&2, Role.Fact>
  {Role.edges(fs) == Laws.role.edges(fs) : List<&2, Imports.Edge>}

def rf.edges(fs):
  match fs:
    case Nil{}:
      {==}
    case Con{Role.Fact{+norm, +deps, +named, +entry}, +rest}:
      %Equal.sym(List<&2, Imports.Edge>, Role.edges(rest), Laws.role.edges(rest), rf.edges(rest)) :
        {Imports.Edge{norm, deps} <> _ == Laws.role.edges(Role.Fact{norm, deps, named, entry} <> rest)
          : List<&2, Imports.Edge>}
      {==}

# the paths of the facts are the law's
law rf.paths:
  for fs: List<&2, Role.Fact>
  {Role.paths(fs) == Laws.role.paths(fs) : List<&2, String>}

def rf.paths(fs):
  match fs:
    case Nil{}:
      {==}
    case Con{Role.Fact{+norm, +deps, +named, +entry}, +rest}:
      %Equal.sym(List<&2, String>, Role.paths(rest), Laws.role.paths(rest), rf.paths(rest)) :
        {norm <> _ == Laws.role.paths(Role.Fact{norm, deps, named, entry} <> rest) : List<&2, String>}
      {==}

# the roots of the laws are the law's
law rf.roots:
  for fs: List<&2, Role.Fact>
  {Role.roots(fs) == Laws.role.roots(fs) : List<&2, String>}

def rf.roots(fs):
  match fs:
    case Nil{}:
      {==}
    case Con{Role.Fact{+norm, +deps, +named, +entry}, +rest}:
      %Equal.sym(List<&2, String>, Role.roots(rest), Laws.role.roots(rest), rf.roots(rest)) :
        {Bool.pick(List<&2, String>, Role.is_law_file(named), norm <> _, _)
          == Laws.role.roots(Role.Fact{norm, deps, named, entry} <> rest) : List<&2, String>}
      {==}

# the roots of the law files are the law's
law rf.lawful:
  for fs: List<&2, Role.Fact>
  {Role.lawful(fs) == Laws.role.lawful(fs) : List<&2, String>}

def rf.lawful(fs):
  match fs:
    case Nil{}:
      {==}
    case Con{Role.Fact{+norm, +deps, +named, +entry}, +rest}:
      %Equal.sym(List<&2, String>, Role.lawful(rest), Laws.role.lawful(rest), rf.lawful(rest)) :
        {Bool.pick(List<&2, String>, Role.is_laws(named), norm <> _, _)
          == Laws.role.lawful(Role.Fact{norm, deps, named, entry} <> rest) : List<&2, String>}
      {==}

# the roots of the code, asked of the index of what the laws reach, are the
# law's over the list
law rf.code:
  for fs: List<&2, Role.Fact>
  for +laws: List<&2, String>
  {Role.code.fast(fs, Bind.index(laws)) == Laws.role.code(fs, laws) : List<&2, String>}

def rf.code(fs, laws):
  match fs:
    case Nil{}:
      {==}
    case Con{Role.Fact{+norm, +deps, +named, +entry}, +rest}:
      +fast = Role.code.fast(rest, Bind.index(laws))
      %Equal.sym(Bool, Bind.indexed(Bind.index(laws), norm), List.contains(~String, ~String.eq, laws, norm),
        M1.ic.indexed(laws, norm)) :
        {Bool.pick(List<&2, String>, Bool.or(entry, Bool.not(_)), norm <> fast, fast)
          == Laws.role.code(Role.Fact{norm, deps, named, entry} <> rest, laws) : List<&2, String>}
      %Equal.sym(List<&2, String>, fast, Laws.role.code(rest, laws), rf.code(rest, laws)) :
        {Bool.pick(List<&2, String>, Bool.or(entry, Bool.not(List.contains(~String, ~String.eq, laws, norm))),
          norm <> _, _) == Laws.role.code(Role.Fact{norm, deps, named, entry} <> rest, laws) : List<&2, String>}
      {==}

# the marks over the indexes of three reaches are the law's over the three
law rf.marks:
  for fs: List<&2, Role.Fact>
  for +laws: List<&2, String>
  for +lawful: List<&2, String>
  for +code: List<&2, String>
  {Role.marks.fast(fs, Bind.index(laws), Bind.index(lawful), Bind.index(code))
    == Laws.role.marks(fs, laws, lawful, code) : List<&2, Role.Mark>}

def rf.marks(fs, laws, lawful, code):
  match fs:
    case Nil{}:
      {==}
    case Con{Role.Fact{+norm, +deps, +named, +entry}, +rest}:
      +fast = Role.marks.fast(rest, Bind.index(laws), Bind.index(lawful), Bind.index(code))
      +goal = Laws.role.marks(Role.Fact{norm, deps, named, entry} <> rest, laws, lawful, code)
      +inl = List.contains(~String, ~String.eq, laws, norm)
      +inc = List.contains(~String, ~String.eq, code, norm)
      +inf = List.contains(~String, ~String.eq, lawful, norm)
      %Equal.sym(Bool, Bind.indexed(Bind.index(laws), norm), inl, M1.ic.indexed(laws, norm)) :
        {Bool.pick(List<&2, Role.Mark>, Bool.and(_, Bool.not(Bind.indexed(Bind.index(code), norm))),
          Role.Mark{norm, Role.role.of(named, Role.reached(Bind.indexed(Bind.index(lawful), norm)))} <> fast, fast)
          == goal : List<&2, Role.Mark>}
      %Equal.sym(Bool, Bind.indexed(Bind.index(code), norm), inc, M1.ic.indexed(code, norm)) :
        {Bool.pick(List<&2, Role.Mark>, Bool.and(inl, Bool.not(_)),
          Role.Mark{norm, Role.role.of(named, Role.reached(Bind.indexed(Bind.index(lawful), norm)))} <> fast, fast)
          == goal : List<&2, Role.Mark>}
      %Equal.sym(Bool, Bind.indexed(Bind.index(lawful), norm), inf, M1.ic.indexed(lawful, norm)) :
        {Bool.pick(List<&2, Role.Mark>, Bool.and(inl, Bool.not(inc)),
          Role.Mark{norm, Role.role.of(named, Role.reached(_))} <> fast, fast) == goal : List<&2, Role.Mark>}
      %Equal.sym(List<&2, Role.Mark>, fast, Laws.role.marks(rest, laws, lawful, code),
        rf.marks(rest, laws, lawful, code)) :
        {Bool.pick(List<&2, Role.Mark>, Bool.and(inl, Bool.not(inc)),
          Role.Mark{norm, Laws.role.given(named, inf)} <> _, _) == goal : List<&2, Role.Mark>}
      {==}

# a search that stops at the first mark is the pick of its role
law rf.either:
  for b: Bool
  for -r: Role.Role
  for -x: Role.Role
  for -y: Role.Role
  for ih: {x == y : Role.Role}
  {Lazy.either(Role.Role, b, _u => r, _v => x) == Bool.pick(Role.Role, b, r, y) : Role.Role}

def rf.either(b, _r, _x, _y, ih):
  match b:
    case True{}:
      {==}
    case False{}:
      ih

def Laws.fact_reads(_path, _text, _toks, _tree, _bound, _items):
  {==}

def Laws.fact_of_text(_path, _text):
  {==}

def Laws.facts_in_order(_s, _ss):
  {==}

def Laws.reach_walks(fs, from):
  %rf.edges(fs) :
    {Role.reach(fs, from)
      == Imports.walk(List.length(&2, Role.Fact, fs), from, from, _, Laws.role.paths(fs)) : List<&2, String>}
  %rf.paths(fs) :
    {Role.reach(fs, from)
      == Imports.walk(List.length(&2, Role.Fact, fs), from, from, Role.edges(fs), _) : List<&2, String>}
  {==}

def Laws.marks_follow_imports(fs):
  +ls = Role.reach(fs, Role.roots(fs))
  +lf = Role.reach(fs, Role.lawful(fs))
  +cd = Role.reach(fs, Role.code(fs, ls))
  %rf.roots(fs) :
    {Role.marks.facts(fs)
      == Laws.role.marks(fs, Role.reach(fs, _), Role.reach(fs, Laws.role.lawful(fs)),
        Role.reach(fs, Laws.role.code(fs, Role.reach(fs, _)))) : List<&2, Role.Mark>}
  %rf.lawful(fs) :
    {Role.marks.facts(fs)
      == Laws.role.marks(fs, ls, Role.reach(fs, _), Role.reach(fs, Laws.role.code(fs, ls)))
      : List<&2, Role.Mark>}
  %rf.code(fs, ls) :
    {Role.marks.facts(fs) == Laws.role.marks(fs, ls, lf, Role.reach(fs, _)) : List<&2, Role.Mark>}
  Equal.sym(List<&2, Role.Mark>, Laws.role.marks(fs, ls, lf, cd), Role.marks.facts(fs),
    Equal.sym(List<&2, Role.Mark>, Role.marks.of(fs, ls, lf, cd), Laws.role.marks(fs, ls, lf, cd),
      rf.marks(fs, ls, lf, cd)))

def Laws.marks_of_run(_ss):
  {==}

def Laws.role_of_first_mark(ms, n):
  match ms:
    case Nil{}:
      {==}
    case Con{Role.Mark{+norm, +role}, +rest}:
      rf.either(String.eq(norm, n), role, Role.of.norm(rest, n), Laws.role.first(rest, n),
        Laws.role_of_first_mark(rest, n))

def Laws.role_of_path(ms, path):
  %Laws.role_of_first_mark(ms, Imports.norm(path)) :
    {Role.of(ms, path)
      == Bool.pick(Role.Role, Role.is_law_file(Role.of_path(path)), Role.of_path(path), _) : Role.Role}
  {==}
