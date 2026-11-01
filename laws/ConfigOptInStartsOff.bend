# An opt-in rule is off unless its own setting names it.
#
# also rests on: laws/LevelOwn.bend
import Base
import ../src/config.bend as Config

# LAW: an opt-in rule with no setting of its own is off, whatever its group
# says (with one, level_own gives it that setting)
law opt_in_off:
  for +sets: List<&2, Config.LevelSet>
  for +group: String
  for +rule: String
  for h_opt: {Config.opt_in(rule) == True{} : Bool}
  for h_rule: {Config.set_level(sets, rule) == None{} : Maybe<&2, Config.Level>}
  {Config.level(Config.Config{sets}, group, rule) == Config.Off{} : Config.Level}
