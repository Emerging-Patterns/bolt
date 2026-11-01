# A rule's level is its own setting, else its group's setting, else its
# group's default.
#
# also rests on: laws/LevelOwn.bend
import Base
import ../src/config.bend as Config

# LAW: nothing is set in an empty config
law set_level_none:
  for name: String
  {Config.set_level([], name) == None{} : Maybe<&2, Config.Level>}

# LAW: a setting of the name, first in file order, is the name's setting
law set_level_first:
  for sets: List<&2, Config.LevelSet>
  for +name: String
  for +nn: String
  for ll: Config.Level
  for h: {String.eq(nn, name) == True{} : Bool}
  {Config.set_level(Config.LevelSet{nn, ll} <> sets, name) == Some{ll} : Maybe<&2, Config.Level>}

# LAW: a setting of another name is passed over
law set_level_skip:
  for +sets: List<&2, Config.LevelSet>
  for +name: String
  for +nn: String
  for ll: Config.Level
  for h: {String.eq(nn, name) == False{} : Bool}
  {Config.set_level(Config.LevelSet{nn, ll} <> sets, name) == Config.set_level(sets, name)
    : Maybe<&2, Config.Level>}

# LAW: a rule with no setting of its own, and not opt-in, is at its group's
# setting
law level_group:
  for +sets: List<&2, Config.LevelSet>
  for +group: String
  for +rule: String
  for +l: Config.Level
  for h_rule: {Config.set_level(sets, rule) == None{} : Maybe<&2, Config.Level>}
  for h_opt: {Config.opt_in(rule) == False{} : Bool}
  for h_group: {Config.set_level(sets, group) == Some{l} : Maybe<&2, Config.Level>}
  {Config.level(Config.Config{sets}, group, rule) == l : Config.Level}

# LAW: a rule with no setting of its own, not opt-in, whose group has no
# setting either, is at its group's default
law level_default:
  for +sets: List<&2, Config.LevelSet>
  for +group: String
  for +rule: String
  for h_rule: {Config.set_level(sets, rule) == None{} : Maybe<&2, Config.Level>}
  for h_opt: {Config.opt_in(rule) == False{} : Bool}
  for h_group: {Config.set_level(sets, group) == None{} : Maybe<&2, Config.Level>}
  {Config.level(Config.Config{sets}, group, rule) == Config.default(group) : Config.Level}
