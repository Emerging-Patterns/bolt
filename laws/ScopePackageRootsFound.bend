# The package roots of a run are `.` and, when bolt lints the whole tree,
# every other directory the walk reads whose listing names a `main.bend` (a
# Bend package's entry file); over files named on the line, `.` is the only
# one. A file's package is the first of its directory and each parent, nearest
# first, that is a package root.
import Base
import ../src/rules.bend as Rules
import ../src/rules/digest.bend as Digest
import ../src/lint/world.bend as W
import ../src/lint/plan.bend as Plan
import ./defs/ScopeWalkFiles.bend as D1

# Packages (laws/ScopePackageRootsFound.bend, laws/ScopeProjectRulesRunOnRoot.bend). A package root other than `.` is a
# directory the walk reads whose listing names a main.bend; `coverage` runs
# on each package's files alone. A directory is named as Digest.dir names one: normalized, with its slash, and
# `` for `.`.

# whether a listing names a main.bend
def names_main(es: List<&2, String>) -> Bool:
  match es:
    case Nil{}:
      False{}
    case Con{e, rest}:
      Bool.or(String.eq(e, "main.bend"), names_main(rest))

# the directories, in order, that are package roots: every one but `.`
# whose listing names a main.bend
def main_dirs(+world: W.World, ds: List<&2, String>) -> List<&2, String>:
  match ds:
    case Nil{}:
      []
    case Con{+d, rest}:
      +more = main_dirs(world, rest)
      Bool.pick(List<&2, String>, Bool.and(Bool.not(String.eq(d, ".")), names_main(W.listing(world, d))), d <> more,
        more)

# LAW: over files named on the line, `.` is the only package root
law roots_named:
  for +world: W.World
  for -p: String
  for -rest: List<&2, String>
  for h: {W.paths.of(world) == p <> rest : List<&2, String>}
  {Plan.roots(world) == [] : List<&2, String>}

# LAW: over the whole tree, the package roots but `.` are the directories the
# walk reads whose listing names a main.bend, in the order it reads them
law roots_whole:
  for +world: W.World
  for h: {W.paths.of(world) == [] : List<&2, String>}
  {Plan.roots(world) == main_dirs(world, Plan.walk.read(Plan.tree(world))) : List<&2, String>}

# LAW: a file's package is the first of its directory and each parent,
# nearest first, that is a package root, and `.` when none is
law package_nearest:
  for +rs: List<&2, String>
  for +dir: String
  {Rules.owner(rs, dir) == D1.nearest(Rules.ups(dir), rs) : String}

# LAW: a directory's parents are read nearest first: the directory itself,
# with its slash, then the parents of what is above it
law ups_nearest_first:
  for s: String
  for +rest: List<&2, String>
  {Rules.ups.go(s <> rest) == (String.join(List.reverse(&2, String, s <> rest), "/") ++ "/") <> Rules.ups.go(rest)
    : List<&2, String>}
