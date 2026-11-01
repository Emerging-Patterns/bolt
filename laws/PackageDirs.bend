import Base
import ../src/lint/plan.bend as Plan
import ./defs/GradedFindingCounts.bend as D1

# LAW: a package root is taken as its directory
law package_dirs:
  for rs: List<&2, String>
  {Plan.packages(rs) == D1.pkgs(rs) : List<&2, String>}
