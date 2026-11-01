# Grading drops a finding at `off` and attaches the level to every other.
import Base
import ../src/config.bend as Config
import ../src/finding.bend as F
import ../src/rules.bend as Rules
import ./defs/GradingKeepsFindings.bend as D1

# LAW: grading drops each finding whose rule is at off and attaches its
# rule's level to every other, in order
law graded_keeps:
  for +cfg: Config.Config
  for fs: List<&2, F.Finding>
  {Rules.graded(cfg, fs) == D1.kept(cfg, fs) : List<&2, F.Graded>}
