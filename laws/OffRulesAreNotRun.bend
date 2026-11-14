# bolt does not run a per-file rule that the file's config sets off, and
# grades the same findings as if it had run every rule, each at the limits
# that config sets. Grading drops an off
# rule's findings, and each rule's findings carry its own slug (Rules.on.slug
# names them for it), so what is not run would have been dropped whole.
import Base
import ../src/config.bend as Config
import ../src/finding.bend as F
import ../src/role.bend as Role
import ../src/src.bend as Src
import ../src/rules.bend as Rules
import ../src/lint/world.bend as W
import ../src/lint/plan.bend as Plan

# LAW: over one file, grading the findings of the rules its config does not
# set off gives what grading every rule's findings gives
law live_grades_alike:
  for +cfg: Config.Config
  for +r: Role.Role
  for +s: Src.Src
  {Rules.graded(cfg, Rules.on.role.live(cfg, r, s)) == Rules.graded(cfg, Rules.on.role(cfg, r, s))
    : List<&2, F.Graded>}

# LAW: over a run, the graded findings with each file's off rules not run
# are the graded findings with every rule run
law final_live:
  for +world: W.World
  {Plan.final.live(world) == Plan.final(world) : List<&2, F.Graded>}
