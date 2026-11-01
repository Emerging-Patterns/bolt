# A bolt.bend is read, never linted, even when named.
import Base
import ../src/rules/laws/law.bend as Law
import ../src/lint/world.bend as W
import ../src/lint/plan.bend as Plan

# whether no path is a bolt.bend. Law vocabulary.
def no_config(ps: List<&2, String>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case Con{+p, rest}:
      +more = no_config(rest)
      Bool.and(Bool.not(Plan.is_config(p)), more)

# LAW: no path the planner lints is a bolt.bend, whatever the command line
# names: a bolt.bend is only ever read, as a candidate config
law no_config_linted:
  for +world: W.World
  {no_config(Plan.inputs(world)) == True{} : Bool}
