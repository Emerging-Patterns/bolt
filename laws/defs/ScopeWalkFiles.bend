# the planner's directory walk, package roots and the .bend files found
import Base
import ../../src/finding.bend as F
import ../../src/rules.bend as Rules
import ../../src/src.bend as Src
import ../../src/role.bend as Role
import ../../src/rules/digest.bend as Digest
import ../../src/rules/laws/law.bend as Law
import ../../src/rules/suspicious/spare.bend as Spare
import ../../src/lint/world.bend as W

# whether a directory is among the roots
def listed(rs: List<&2, String>, +d: String) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case Con{r, rest}:
      Bool.or(String.eq(r, d), listed(rest, d))

# the first of the directories that is a root, or `` (the package `.`)
def nearest(us: List<&2, String>, +rs: List<&2, String>) -> String:
  match us:
    case Nil{}:
      ""
    case Con{+u, rest}:
      +more = nearest(rest, rs)
      Bool.pick(String, listed(rs, u), u, more)

# the files of one package, in order
def part(ds: List<&2, Digest.Digest>, +rs: List<&2, String>, +pkg: String) -> List<&2, Digest.Digest>:
  match ds:
    case Nil{}:
      []
    case Con{Digest.Digest{path, norm, +dir, is_laws, is_law_file, exempt, tops, says, deps, laws, links}, rest}:
      +more = part(rest, rs, pkg)
      Bool.pick(List<&2, Digest.Digest>, String.eq(nearest(Rules.ups(dir), rs), pkg),
        Digest.Digest{path, norm, dir, is_laws, is_law_file, exempt, tops, says, deps, laws, links} <> more, more)

# `coverage` on the files of each package but `.`
def covered(ps: List<&2, String>, +ds: List<&2, Digest.Digest>, +rs: List<&2, String>) -> List<&2, F.Finding>:
  match ps:
    case Nil{}:
      []
    case Con{+dir, rest}:
      List.append(&2, F.Finding, Law.check(part(ds, rs, dir)), covered(rest, ds, rs))

# the project rules' findings: `coverage` on each package's files, `.`
# first, then `spare` on every file's at once
def packed(+srcs: List<&2, Src.Src>, +rs: List<&2, String>) -> List<&2, F.Finding>:
  +ds = Digest.all.role(Role.marks(srcs), srcs)
  List.append(&2, F.Finding, List.concat(&2, F.Finding, [Law.check(part(ds, rs, "")), covered(rs, ds, rs)]),
    Spare.check(ds))

# The walk (laws/ScopeWalksWholeTree.bend). With no paths named, the planner lints what a
# breadth-first search over the World's listings reaches from `.`. The spec
# below writes that search apart from plan.bend's walk, which threads a queue,
# the files found so far and the directories read through one fuelled loop:
# here the directories read come first, in order, and their files are
# gathered after. walk_bfs holds for every bound on the directories read;
# walk_files is the row, at 100000.

# an entry's name without the "/" that marks a directory
def entry_name(+e: String) -> String:
  String.take(e, Nat.sub(String.length(e), 1n))

# whether an entry is a directory the search descends into: it ends in "/",
# and its name neither starts with "." (hidden) nor is node_modules
def descends(+e: String) -> Bool:
  +n = entry_name(e)
  Bool.and(String.ends_with(e, "/"), Bool.not(Bool.or(String.starts_with(n, "."), String.eq(n, "node_modules"))))

# the directories a listing of a directory names and the search descends
# into, as paths, in listing order
def subdirs(es: List<&2, String>, +dir: String) -> List<&2, String>:
  match es:
    case Nil{}:
      []
    case Con{+e, rest}:
      +more = subdirs(rest, dir)
      Bool.pick(List<&2, String>, descends(e), (dir ++ "/" ++ entry_name(e)) <> more, more)

# the `.bend` files a listing of a directory names, as paths, in listing
# order
def bends_in(es: List<&2, String>, +dir: String) -> List<&2, String>:
  match es:
    case Nil{}:
      []
    case Con{+e, rest}:
      +more = bends_in(rest, dir)
      Bool.pick(List<&2, String>, String.ends_with(e, ".bend"), (dir ++ "/" ++ e) <> more, more)

# the directories a breadth-first search from the queue reads, in the order
# it reads them, at most `reads` of them: each is listed, and the ones its
# listing names that the search descends into join the back of the queue.
# Past that bound the search stops, and says nothing.
def bfs(reads: Nat, +world: W.World, queue: List<&2, String>) -> List<&2, String>:
  match reads:
    case 0n:
      []
    case 1n+f:
      match queue:
        case Nil{}:
          []
        case Con{+d, rest}:
          d <> bfs(f, world, List.append(&2, String, rest, subdirs(W.listing(world, d), d)))

# the `.bend` files the listings of the directories name, the last directory
# read first (the order the planner sorts from)
def found_in(ds: List<&2, String>, +world: W.World) -> List<&2, String>:
  match ds:
    case Nil{}:
      []
    case Con{+d, rest}:
      List.append(&2, String, found_in(rest, world), bends_in(W.listing(world, d), d))
