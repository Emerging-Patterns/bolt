# the package directories list
import Base
import ../../src/lint/plan.bend as Plan
import ../../src/rules/imports.bend as Imports
import ../../laws/PackageDirs.bend as L1
import ../../laws/defs/GradedFindingCounts.bend as D1

def L1.package_dirs(rs):
  match rs:
    case Nil{}:
      {==}
    case Con{r, +tl}:
      Equal.cong(List<&2, String>, List<&2, String>, xs => Imports.dir_of(r ++ "/main.bend") <> xs,
        Plan.packages(tl), D1.pkgs(tl), L1.package_dirs(tl))
