import Base
import ../src/config.bend as Config

# LAW: a rule's own setting is its level, whatever its group says, an
# opt-in rule's too
law level_own:
  for lims: List<&2, Config.Limit>
  for +sets: List<&2, Config.LevelSet>
  for +group: String
  for +rule: String
  for +l: Config.Level
  for h: {Config.set_level(sets, rule) == Some{l} : Maybe<&2, Config.Level>}
  {Config.level(Config.Config{sets, lims}, group, rule) == l : Config.Level}
