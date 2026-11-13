# `bolt <files>` lints only the files it is given, but a file's role follows
# the imports of the whole tree (laws/RoleFollowsImports.bend): the main.bend
# that makes a named file code, or the LAWS.bend that makes it a law file,
# need not be named. So a run over named files reads every source the walk of
# the tree finds for its imports, each at its path resolved against the
# working directory, takes the marks of that graph, and looks each named file
# up there as it is spelled. The graph is every source the walk finds, then
# each named file the walk did not find (one outside the working directory),
# so no file is read twice and none named is left out. A run over the whole tree takes the marks of its
# own sources.
import Base
import ../src/src.bend as Src
import ../src/role.bend as Role
import ../src/lint/world.bend as W
import ../src/lint/plan.bend as Plan
import ../src/rules/imports.bend as Imports

# LAW: a path that starts at the root is the file it names, normalized
law abs_keeps_rooted:
  for +cwd: String
  for +path: String
  for e: {String.starts_with(path, "/") == True{} : Bool}
  {Plan.abs(cwd, path) == Imports.norm(path) : String}

# LAW: any other path is resolved against the working directory, then
# normalized, so two spellings of one file are one path
law abs_resolves_relative:
  for +cwd: String
  for +path: String
  for e: {String.starts_with(path, "/") == False{} : Bool}
  {Plan.abs(cwd, path) == Imports.norm(cwd ++ "/" ++ path) : String}

# LAW: paths are resolved one by one, in order
law norms_in_order:
  for p: String
  for rest: List<&2, String>
  for +cwd: String
  {Plan.norms(p <> rest, cwd) == Plan.abs(cwd, p) <> Plan.norms(rest, cwd) : List<&2, String>}

# LAW: a file the World read gives the graph its fact, read from its text at
# its resolved path, in order
law facts_of_read:
  for path: String
  for text: String
  for rest: List<&2, Plan.Got>
  for +cwd: String
  {Plan.facts.of(Plan.Got{path, Some{text}} <> rest, cwd)
    == Role.fact.text(Plan.abs(cwd, path), text) <> Plan.facts.of(rest, cwd) : List<&2, Role.Fact>}

# LAW: a file the World could not read gives the graph nothing
law facts_of_unread:
  for path: String
  for rest: List<&2, Plan.Got>
  for +cwd: String
  {Plan.facts.of(Plan.Got{path, None{}} <> rest, cwd) == Plan.facts.of(rest, cwd) : List<&2, Role.Fact>}

# LAW: each named file is marked as it is spelled, normalized, with the role
# the marks hold at its resolved path, in order
law marks_keyed_as_spelled:
  for +p: String
  for rest: List<&2, String>
  for +cwd: String
  for +ms: List<&2, Role.Mark>
  {Plan.marks.key(p <> rest, cwd, ms)
    == Role.Mark{Imports.norm(p), Role.of.norm(ms, Plan.abs(cwd, p))} <> Plan.marks.key(rest, cwd, ms)
    : List<&2, Role.Mark>}

# LAW: the marks of a run over named files are the run's sources keyed among
# the marks of the whole tree's graph, every file of it read for its imports
law marks_named_read_the_tree:
  for +world: W.World
  {Plan.marks.named(world)
    == Plan.marks.key(Plan.inputs(world), W.cwd.of(world),
      Role.marks.facts(Plan.facts.of(Plan.gots(Plan.graph(world), world), W.cwd.of(world))))
    : List<&2, Role.Mark>}

# LAW: a run with files named takes the marks of the whole tree's graph
law marks_run_named:
  for p: String
  for rest: List<&2, String>
  for +world: W.World
  for +ss: List<&2, Src.Src>
  {Plan.marks.run(p <> rest, world, ss) == Plan.marks.named(world) : List<&2, Role.Mark>}

# LAW: a run over the whole tree takes the marks of its own sources
law marks_run_whole_tree:
  for +world: W.World
  for +ss: List<&2, Src.Src>
  {Plan.marks.run(Nil{}, world, ss) == Role.marks(ss) : List<&2, Role.Mark>}

# LAW: a named file that resolves to a path already seen is not read again
law unseen_drops_seen:
  for +p: String
  for rest: List<&2, String>
  for +cwd: String
  for +seen: List<&2, String>
  for e: {Imports.has(seen, Plan.abs(cwd, p)) == True{} : Bool}
  {Plan.unseen(p <> rest, cwd, seen) == Plan.unseen(rest, cwd, seen) : List<&2, String>}

# LAW: a named file that resolves to no path seen is read, in the order named
law unseen_keeps_new:
  for +p: String
  for rest: List<&2, String>
  for +cwd: String
  for +seen: List<&2, String>
  for e: {Imports.has(seen, Plan.abs(cwd, p)) == False{} : Bool}
  {Plan.unseen(p <> rest, cwd, seen) == p <> Plan.unseen(rest, cwd, seen) : List<&2, String>}

# LAW: the graph is the sources the walk finds, then the named files it did
# not find
law graph_found_then_named:
  for +world: W.World
  {Plan.graph(world)
    == List.append(&2, String, Plan.sources(Plan.walk.found(Plan.tree(world))),
      Plan.unseen(Plan.inputs(world), W.cwd.of(world),
        Plan.norms(Plan.sources(Plan.walk.found(Plan.tree(world))), W.cwd.of(world))))
    : List<&2, String>}
