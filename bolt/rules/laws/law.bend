# rule law (project-wide): in a project that states laws (a directory with a
# LAWS.bend), every def is named by some law, IO included. A def a law never
# mentions has no stated property: it is the coverage gap. A type is covered
# once any law reaches its module (a law about an instance names the
# accessors, never the service type). Out of scope: helpers (dotted names),
# tests, and the law files themselves. `main` is a def: a law that names it
# covers it. The rule reads each file's digest (bolt/rules/digest.bend),
# never the parsed source: its phases use the list three times, and a `+`
# reuse copies it.
import Base
import ../../../lazy/lazy.bend as Lazy
import ../../finding.bend as F
import ../../../syntax/outline.bend as Outline
import ../digest.bend as Digest

# what the laws name
# ------------------

# what the laws of every file name
def named(ds: List<&2, Digest.Digest>) -> List<&2, Digest.Mention>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{Digest.Digest{path, norm, dir, is_laws, is_law_file, exempt, tops, says, deps, unsafes}, rest}:
      List.append(&2, Digest.Mention, says, named(rest))

# is the item named?
def has_item(ms: List<&2, Digest.Mention>, +pp: String, +name: String) -> Bool:
  match ms:
    case Nil{}:
      False{}
    case Con{Digest.Mention{+mp, +mn}, rest}:
      Lazy.or_else(Bool.and(String.eq(mp, pp), String.eq(mn, name)), _u => has_item(rest, pp, name))

# is anything of the module named?
def has_module(ms: List<&2, Digest.Mention>, +pp: String) -> Bool:
  match ms:
    case Nil{}:
      False{}
    case Con{Digest.Mention{+mp, mn}, rest}:
      Lazy.or_else(String.eq(mp, pp), _u => has_module(rest, pp))

# what is in scope
# ----------------

# the directories that state laws
def law_dirs(ds: List<&2, Digest.Digest>) -> List<&2, String>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{Digest.Digest{path, norm, dir, is_laws, is_law_file, exempt, tops, says, deps, unsafes}, rest}:
      +more = law_dirs(rest)
      Bool.pick(List<&2, String>, is_laws, dir <> more, more)

# is the path under one of the directories?
def under(dirs: List<&2, String>, +pp: String) -> Bool:
  match dirs:
    case Nil{}:
      False{}
    case Con{d, rest}:
      Lazy.or_else(String.starts_with(pp, d), _u => under(rest, pp))

# a def or a type that no law reaches
def gaps(ts: List<&2, Digest.Top>, +ms: List<&2, Digest.Mention>, +pp: String, +path: String) ->
  List<&2, F.Finding>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{Digest.Top{Outline.IDef{}, +name, +line}, rest}:
      +more = gaps(rest, ms, pp, path)
      Bool.pick(List<&2, F.Finding>,
        Bool.or(String.contains(name, "."), has_item(ms, pp, name)), more,
        F.Finding{path, line, 0, 0, "law", "def " ++ name ++ " is named by no law"} <> more)
    case Con{Digest.Top{Outline.IType{}, +name, +line}, rest}:
      +more = gaps(rest, ms, pp, path)
      Bool.pick(List<&2, F.Finding>, has_module(ms, pp), more,
        F.Finding{path, line, 0, 0, "law", "type " ++ name ++ ": no law reaches this module"} <> more)
    case Con{other, rest}:
      gaps(rest, ms, pp, path)

# every file in scope, against what the laws name. A file out of scope pays
# nothing: `gaps` scans what the laws name once for each def, and as an
# argument of a `Bool.pick` it ran on every file the linter read, laws or no
# laws (50 files of a project with no LAWS.bend cost 88 s that way).
def check.go(ds: List<&2, Digest.Digest>, +dirs: List<&2, String>, +ms: List<&2, Digest.Mention>) ->
  List<&2, F.Finding>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{Digest.Digest{path, +norm, dir, is_laws, is_law_file, exempt, tops, says, deps, unsafes}, rest}:
      +more = check.go(rest, dirs, ms)
      Lazy.stop(List<&2, F.Finding>, Bool.or(exempt, Bool.not(under(dirs, norm))), more,
        _u => List.append(&2, F.Finding, gaps(tops, ms, norm, path), more))

# a project states no laws: nothing of it is under law, and what its laws
# would name is never gathered
def check.first(+ds: List<&2, Digest.Digest>, dirs: List<&2, String>) -> List<&2, F.Finding>:
  match dirs:
    case Nil{}:
      Nil{}
    case Con{d, rest}:
      check.go(ds, d <> rest, named(ds))

# the rule, over every file the linter read
def check(+ds: List<&2, Digest.Digest>) -> List<&2, F.Finding>:
  check.first(ds, law_dirs(ds))
