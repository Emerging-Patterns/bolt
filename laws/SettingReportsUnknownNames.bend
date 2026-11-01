# `setting` reports exactly, for each bolt.bend that grades a directory the
# run grades (a source's; the first of its candidates the World
# read, laws/ConfigNearestFileGrades.bend), each bolt.bend once in the order its directories come,
# one finding for each setting `unknown` holds (laws/ConfigUnknownSettingsFound.bend), at that
# bolt.bend's path and the line of the setting's `def`, in file order, and
# nothing else. It runs in the CLI lint only.
#
# also rests on: laws/UnknownExact.bend
import Base
import ../src/finding.bend as F
import ../src/lint/world.bend as W
import ../src/lint/plan.bend as Plan
import ./defs/GradedFindingCounts.bend as D1

# LAW: `setting` reports, for each bolt.bend that grades a directory of the
# run, each bolt.bend once in the order its directories come, one finding for
# each setting `unknown` holds, at that bolt.bend's path and the line of the
# setting's def, in file order, and nothing else
law setting_reports:
  for +world: W.World
  {Plan.settings(world) == D1.settings_found(world) : List<&2, F.Finding>}
