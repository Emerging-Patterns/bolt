# part of: laws/OutputSummaryAndExitStatus.bend,
# laws/NoqaSilencesNamedFindings.bend
import Base
import ../src/lint/world.bend as W
import ../src/lint/plan.bend as Plan
import ./defs/GradedFindingCounts.bend as D1

# LAW: the last line is `clean` or `N errors, M warnings` for the graded
# findings no noqa comment silenced, `noqa`'s own included
law last_line_summary:
  for +world: W.World
  {List.last(&2, String, Plan.lines.of(Plan.plan(world))) == Some{D1.summary_of(D1.run_graded(world))}
    : Maybe<&2, String>}
