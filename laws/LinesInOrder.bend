import Base
import ../src/finding.bend as F
import ../src/rules.bend as Rules
import ../src/lint/world.bend as W
import ../src/lint/plan.bend as Plan
import ./defs/GradedFindingCounts.bend as D1

# each graded finding's line, in order
def shown_all(gs: List<&2, F.Graded>) -> List<&2, String>:
  match gs:
    case Nil{}:
      Nil{}
    case Con{g, rest}:
      F.show_graded(g) <> shown_all(rest)

# the lines a run prints: each graded finding, in order, then the summary
def out_lines(+world: W.World) -> List<&2, String>:
  +gs = D1.run_graded(world)
  List.append(&2, String, shown_all(gs), [D1.summary_of(gs)])

# LAW: `bolt` prints the read failures, then the per-file findings in
# file-list order and `Rules.on` order, then `setting`'s, then coverage and
# unsafe, each graded finding as one line, the ones at off dropped
# and the ones a noqa comment on their line names dropped, then `noqa`'s
# findings, then the summary
law lines_in_order:
  for +world: W.World
  {Plan.lines.of(Plan.plan(world)) == out_lines(world) : List<&2, String>}
