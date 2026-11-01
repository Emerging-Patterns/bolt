# proofs of laws/ScopeWalksWholeTree.bend
import Base
import ../src/lint/world.bend as W
import ../src/lint/plan.bend as Plan
import ../laws/ScopeWalksWholeTree.bend as Laws
import ../laws/WalkBfs.bend as L1
import ../laws/defs/ScopeWalkFiles.bend as D1
import ./lemmas/PlannerWalkInduction.bend as M1

def Laws.walk_files(world, h):
  e = Equal.sym(List<&2, String>, W.paths.of(world), [], h)
  %e : {Plan.files.named(_, world)
    == List.sort(~String, ~String.is_le, D1.found_in(D1.bfs(100000n, world, ["."]), world))
    : List<&2, String>}
  Equal.cong(List<&2, String>, List<&2, String>, xs => List.sort(~String, ~String.is_le, xs),
    Plan.walk.found(Plan.tree(world)), D1.found_in(D1.bfs(100000n, world, ["."]), world),
    L1.walk_bfs(100000n, world))
