# rule law (project-wide): in a project that states laws (a directory with a
# LAWS.bend), every def is named by a quantified law in a LAWS.bend: its
# binders or its statement use the def, through an import alias or in the
# law's own file. A def no such law names has no stated property: it is the
# coverage gap. A closed law, a law's own name, and a law outside a LAWS.bend
# name nothing. A type is covered when such a law names it or a def of its
# module (a law about an instance names the accessors, never the service
# type). Out of scope: helpers (dotted names), tests, and the law
# files themselves -- decided by the def's name and the file's path, never by
# what the file's text mentions. IO is no exemption: a law can quantify over
# an IO value or state an IO equality, so a def returning `IO(..)` is graded
# like any other, and so is every pure def beside it. `main` is a def: a law
# that names it covers it. The rule reads each file's digest
# (bolt/rules/digest.bend), never the parsed source: its phases use the list
# three times, and a `+` reuse copies it.
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

# is some def of the module named? (a law about an instance names the
# accessors, never the service type)
def reached(ts: List<&2, Digest.Top>, +ms: List<&2, Digest.Mention>, +pp: String) -> Bool:
  match ts:
    case Nil{}:
      False{}
    case Con{Digest.Top{Outline.IDef{}, +name, line}, rest}:
      Lazy.or_else(has_item(ms, pp, name), _u => reached(rest, ms, pp))
    case Con{other, rest}:
      reached(rest, ms, pp)

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
def gaps(
  ts: List<&2, Digest.Top>,
  +ms: List<&2, Digest.Mention>,
  +pp: String,
  +path: String,
  +hit: Bool
) -> List<&2, F.Finding>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{Digest.Top{Outline.IDef{}, +name, +line}, rest}:
      +more = gaps(rest, ms, pp, path, hit)
      Bool.pick(List<&2, F.Finding>,
        Bool.or(String.contains(name, "."), has_item(ms, pp, name)), more,
        F.Finding{path, line, 0, 0, "law", "Def " ++ name ++ " is named by no law."} <> more)
    case Con{Digest.Top{Outline.IType{}, +name, +line}, rest}:
      +more = gaps(rest, ms, pp, path, hit)
      Bool.pick(List<&2, F.Finding>, Bool.or(hit, has_item(ms, pp, name)), more,
        F.Finding{path, line, 0, 0, "law", "Type " ++ name ++ ": no law reaches this module."} <> more)
    case Con{other, rest}:
      gaps(rest, ms, pp, path, hit)

# every file in scope, against what the laws name. A file out of scope pays
# nothing: `gaps` scans what the laws name once for each def, and as an
# argument of a `Bool.pick` it ran on every file the linter read, laws or no
# laws (50 files of a project with no LAWS.bend cost 88 s that way).
def check.go(
  ds: List<&2, Digest.Digest>,
  +dirs: List<&2, String>,
  +ms: List<&2, Digest.Mention>
) -> List<&2, F.Finding>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{Digest.Digest{path, +norm, dir, is_laws, is_law_file, exempt, +tops, says, deps, unsafes}, rest}:
      +more = check.go(rest, dirs, ms)
      Lazy.stop(List<&2, F.Finding>, Bool.or(exempt, Bool.not(under(dirs, norm))), more,
        _u => List.append(&2, F.Finding, gaps(tops, ms, norm, path, reached(tops, ms, norm)), more))

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
