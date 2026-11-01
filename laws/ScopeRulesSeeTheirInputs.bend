# A per-file rule sees one file's `Src`; `coverage` sees the digests of one
# package's files (laws/ScopePackageRootsFound.bend) at a time; `setting` sees the text of each
# bolt.bend grading reads; and nothing else.
#
# also rests on: laws/PackagesScoped.bend
import Base
import ../src/finding.bend as F
import ../src/src.bend as Src
import ../src/lint/world.bend as W
import ../src/lint/plan.bend as Plan
import ./defs/GradedFindingCounts.bend as D1

# LAW: the planner's findings are the read failures, then the per-file rules
# on each source's Src and role, then `setting` on each bolt.bend grading reads,
# then the project rules on the digests of every source in the run, and
# nothing else
law scope_findings:
  for +world: W.World
  {Plan.found(world) == D1.in_scope(world) : List<&2, F.Finding>}
