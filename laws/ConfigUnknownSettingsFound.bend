# A setting in a bolt.bend whose name is no rule or group is a finding: of the
# settings grading reads from a bolt.bend (each `def` whose body holds a
# string), `unknown` holds exactly those whose name is neither the slug nor
# the group of any row of the code table, in file order, one each.
#
# also rests on: laws/UnknownExact.bend
import Base
import ../src/config.bend as Config

# LAW: the settings `unknown` judges are the ones grading reads: a bolt.bend's
# config is its settings, in file order, each at the level its word gives
law settings_graded:
  for text: String
  {Config.parse(text) == Config.Config{Config.levels(Config.settings(text))} : Config.Config}
