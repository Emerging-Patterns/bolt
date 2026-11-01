import Base
import ../src/lint/world.bend as W
import ../src/lint/plan.bend as Plan
import ./defs/ScopeWalkFiles.bend as D1

# LAW: the walk from `.`, reading at most `reads` directories, finds the
# `.bend` files of the directories the breadth-first search reads within that
# bound: those its listings name, and none from a directory it does not
# descend into (hidden, or node_modules) or does not reach before the bound
law walk_bfs:
  for +reads: Nat
  for +world: W.World
  {Plan.walk.found(Plan.walk(reads, world, ["."], [], [])) == D1.found_in(D1.bfs(reads, world, ["."]), world)
    : List<&2, String>}
