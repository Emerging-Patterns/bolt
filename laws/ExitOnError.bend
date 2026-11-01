# part of: laws/OutputSummaryAndExitStatus.bend,
# laws/NoqaSilencesNamedFindings.bend
import Base
import ../src/config.bend as Config
import ../src/finding.bend as F
import ../src/lint/world.bend as W
import ../src/lint/plan.bend as Plan
import ./defs/GradedFindingCounts.bend as D1

# true at error, or what the rest says
def any_error.one(ll: Config.Level, more: Bool) -> Bool:
  match ll:
    case Config.Off{}:
      more
    case Config.Warn{}:
      more
    case Config.Error{}:
      True{}

# whether some graded finding is at error
def any_error(gs: List<&2, F.Graded>) -> Bool:
  match gs:
    case Nil{}:
      False{}
    case Con{F.Graded{ll, _ff}, rest}:
      any_error.one(ll, any_error(rest))

# LAW: the exit status is 1 exactly when some graded finding is an error,
# and 0 otherwise, a silenced finding counting for nothing
law exit_on_error:
  for +world: W.World
  {Plan.exit.of(Plan.plan(world)) == Bool.pick(U32, any_error(D1.run_graded(world)), 1, 0) : U32}
