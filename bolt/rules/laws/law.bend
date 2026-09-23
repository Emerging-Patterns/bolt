# rule coverage (project-wide; its module is law.bend, since `law` is a Bend
# keyword and no bolt.bend could name it): in a project that states laws (a
# LAWS.bend among the files the linter read), every def and type of every
# file is named by a quantified law in a LAWS.bend: its binders or its
# statement use it, through an import alias or in the law's own file. A def
# no such law names has no stated property: it is the coverage gap. A closed
# law, a law's own name, and a law outside a LAWS.bend name nothing. A type is
# covered when such a law names it or one of its constructors (`M.Sq{..}`
# covers a `type Shape` with `Sq{..}`); a law that names only another def of
# its module does not cover it. Out of scope: helper defs (dotted names; a
# dotted type is graded), tests, and the law files themselves -- decided by
# the name and the file's path, never by what the file's text mentions. IO is
# no exemption: a law can quantify over an IO value or state an IO equality,
# so a def returning `IO(..)` is graded like any other, and so is every pure
# def beside it. `main` is a def: a law that names it covers it. The rule
# reads each file's digest (bolt/rules/digest.bend), never the parsed source:
# its phases use the list three times, and a `+` reuse copies it.
import Base
import ../../../lazy/lazy.bend as Lazy
import ../../finding.bend as F
import ../../../syntax/outline.bend as Outline
import ../digest.bend as Digest

# what the laws name
# ------------------

# a file's uses onto the others', when the file is a LAWS.bend
def named.put(laws: Bool, ms: List<&2, Digest.Mention>, more: List<&2, Digest.Mention>) -> List<&2, Digest.Mention>:
  match laws:
    case True{}:
      List.append(&2, Digest.Mention, ms, more)
    case False{}:
      more

# what the laws of every LAWS.bend name (Digest.of records uses for no
# other file; a digest list handed in from elsewhere is read the same way)
def named(ds: List<&2, Digest.Digest>) -> List<&2, Digest.Mention>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{Digest.Digest{path, norm, dir, is_laws, is_law_file, exempt, tops, says, deps, unsafes, laws}, rest}:
      named.put(is_laws, says, named(rest))

# is the item named?
def has_item(ms: List<&2, Digest.Mention>, +pp: String, +name: String) -> Bool:
  match ms:
    case Nil{}:
      False{}
    case Con{Digest.Mention{+mp, +mn}, rest}:
      Lazy.or_else(Bool.and(String.eq(mp, pp), String.eq(mn, name)), _u => has_item(rest, pp, name))

# is one of the names (a type's constructors) named?
def any_item(ns: List<&2, String>, +ms: List<&2, Digest.Mention>, +pp: String) -> Bool:
  match ns:
    case Nil{}:
      False{}
    case Con{+name, rest}:
      Lazy.or_else(has_item(ms, pp, name), _u => any_item(rest, ms, pp))

# what is in scope
# ----------------

# the directories that state laws
def law_dirs(ds: List<&2, Digest.Digest>) -> List<&2, String>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{Digest.Digest{path, norm, dir, is_laws, is_law_file, exempt, tops, says, deps, unsafes, laws}, rest}:
      +more = law_dirs(rest)
      Bool.pick(List<&2, String>, is_laws, dir <> more, more)

# a def, or a type, that no law names
def gaps(ts: List<&2, Digest.Top>, +ms: List<&2, Digest.Mention>, +pp: String, +path: String) -> List<&2, F.Finding>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{Digest.Top{Outline.IDef{}, +name, +line, cs}, rest}:
      +more = gaps(rest, ms, pp, path)
      Bool.pick(List<&2, F.Finding>,
        Bool.or(String.contains(name, "."), has_item(ms, pp, name)), more,
        F.Finding{path, line, 0, 0, "coverage", "Def " ++ name ++ " is named by no law."} <> more)
    case Con{Digest.Top{Outline.IType{}, +name, +line, cs}, rest}:
      +more = gaps(rest, ms, pp, path)
      Bool.pick(List<&2, F.Finding>, Lazy.or_else(has_item(ms, pp, name), _u => any_item(cs, ms, pp)), more,
        F.Finding{path, line, 0, 0, "coverage", "Type " ++ name ++ " is named by no law, nor are its constructors."}
          <> more)
    case Con{other, rest}:
      gaps(rest, ms, pp, path)

# every file not exempt, against what the laws name. A project with no laws pays
# nothing: `gaps` scans what the laws name once for each def, and as an
# argument of a `Bool.pick` it ran on every file the linter read, laws or no
# laws (50 files of a project with no LAWS.bend cost 88 s that way).
def check.go(ds: List<&2, Digest.Digest>, +ms: List<&2, Digest.Mention>) -> List<&2, F.Finding>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{Digest.Digest{path, +norm, dir, is_laws, is_law_file, exempt, tops, says, deps, unsafes, laws}, rest}:
      +more = check.go(rest, ms)
      Lazy.stop(List<&2, F.Finding>, exempt, more,
        _u => List.append(&2, F.Finding, gaps(tops, ms, norm, path), more))

# a project states no laws: nothing of it is under law, and what its laws
# would name is never gathered
def check.first(+ds: List<&2, Digest.Digest>, dirs: List<&2, String>) -> List<&2, F.Finding>:
  match dirs:
    case Nil{}:
      Nil{}
    case Con{d, rest}:
      check.go(ds, named(ds))

# the rule, over every file the linter read
def check(+ds: List<&2, Digest.Digest>) -> List<&2, F.Finding>:
  check.first(ds, law_dirs(ds))
