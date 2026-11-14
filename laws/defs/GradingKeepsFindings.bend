# what grading keeps of findings at a level, in order, under the config
import Base
import ../../src/config.bend as Config
import ../../src/finding.bend as F
import ../../src/rules.bend as Rules

# a finding at a level onto what grading keeps of the rest: dropped at off,
# kept with its level otherwise
def keep(l: Config.Level, f: F.Finding, rest: List<&2, F.Graded>) -> List<&2, F.Graded>:
  match l:
    case Config.Off{}:
      rest
    case Config.Warn{}:
      F.Graded{Config.Warn{}, f} <> rest
    case Config.Error{}:
      F.Graded{Config.Error{}, f} <> rest

# every finding at the level the config gives its rule, in order, the ones
# at off dropped
def kept(+cfg: Config.Config, fs: List<&2, F.Finding>) -> List<&2, F.Graded>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{F.Finding{path, line, col, len, +rule, msg}, rest}:
      keep(Config.level(cfg, Rules.group(rule), rule), F.Finding{path, line, col, len, rule, msg}, kept(cfg, rest))
