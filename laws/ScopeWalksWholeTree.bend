# With no files named, bolt lints every `.bend` file under `.` found within
# the first 100000 directories the walk reads, not descending into hidden
# directories or `node_modules`, sorted by code point; past that bound the
# walk stops silently.
import Base
import ../src/lint/world.bend as W
import ../src/lint/plan.bend as Plan
import ./defs/ScopeWalkFiles.bend as D1

# LAW: with no paths named, the planner's file list is the `.bend` files the
# search reaches from `.` within the first 100000 directories it reads,
# sorted by code point; past that bound the walk stops silently
law walk_files:
  for +world: W.World
  for h: {W.paths.of(world) == [] : List<&2, String>}
  {Plan.files(world) == List.sort(~String, ~String.is_le, D1.found_in(D1.bfs(100000n, world, ["."]), world))
    : List<&2, String>}
