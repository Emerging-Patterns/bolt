# bolt: the laws. Grading is a pure function of a config and the findings,
# so these laws quantify over every list of settings and every finding,
# never over one bolt.bend.
import Base
import ./config.bend as Config
import ./finding.bend as F
import ./rules.bend as Rules

# LAW: nothing is set in an empty config
# BOLT-CFG-1
law set_level_none:
  for name: String
  {Config.set_level([], name) == None{} : Maybe<&2, Config.Level>}

# LAW: a setting of the name, first in file order, is the name's setting
# BOLT-CFG-1
law set_level_first:
  for sets: List<&2, Config.Set>
  for +name: String
  for +nn: String
  for ll: Config.Level
  for h: {String.eq(nn, name) == True{} : Bool}
  {Config.set_level(Config.Set{nn, ll} <> sets, name) == Some{ll} : Maybe<&2, Config.Level>}

# LAW: a setting of another name is passed over
# BOLT-CFG-1
law set_level_skip:
  for +sets: List<&2, Config.Set>
  for +name: String
  for +nn: String
  for ll: Config.Level
  for h: {String.eq(nn, name) == False{} : Bool}
  {Config.set_level(Config.Set{nn, ll} <> sets, name) == Config.set_level(sets, name)
    : Maybe<&2, Config.Level>}

# LAW: a rule's own setting is its level, whatever its group says, an
# opt-in rule's too
# BOLT-CFG-1
# BOLT-CFG-6
law level_own:
  for +sets: List<&2, Config.Set>
  for +group: String
  for +rule: String
  for +l: Config.Level
  for h: {Config.set_level(sets, rule) == Some{l} : Maybe<&2, Config.Level>}
  {Config.level(Config.Config{sets}, group, rule) == l : Config.Level}

# LAW: a rule with no setting of its own, and not opt-in, is at its group's
# setting
# BOLT-CFG-1
law level_group:
  for +sets: List<&2, Config.Set>
  for +group: String
  for +rule: String
  for +l: Config.Level
  for h_rule: {Config.set_level(sets, rule) == None{} : Maybe<&2, Config.Level>}
  for h_opt: {Config.opt_in(rule) == False{} : Bool}
  for h_group: {Config.set_level(sets, group) == Some{l} : Maybe<&2, Config.Level>}
  {Config.level(Config.Config{sets}, group, rule) == l : Config.Level}

# LAW: a rule with no setting of its own, not opt-in, whose group has no
# setting either, is at its group's default
# BOLT-CFG-1
law level_default:
  for +sets: List<&2, Config.Set>
  for +group: String
  for +rule: String
  for h_rule: {Config.set_level(sets, rule) == None{} : Maybe<&2, Config.Level>}
  for h_opt: {Config.opt_in(rule) == False{} : Bool}
  for h_group: {Config.set_level(sets, group) == None{} : Maybe<&2, Config.Level>}
  {Config.level(Config.Config{sets}, group, rule) == Config.default(group) : Config.Level}

# a finding at a level onto what grading keeps of the rest: dropped at off,
# kept with its level otherwise
def keep(ll: Config.Level, ff: F.Finding, rest: List<&2, F.Graded>) -> List<&2, F.Graded>:
  match ll:
    case Config.Off{}:
      rest
    case Config.Warn{}:
      F.Graded{Config.Warn{}, ff} <> rest
    case Config.Error{}:
      F.Graded{Config.Error{}, ff} <> rest

# every finding at the level the config gives its rule, in order, the ones
# at off dropped
def kept(+cfg: Config.Config, fs: List<&2, F.Finding>) -> List<&2, F.Graded>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{F.Finding{path, line, col, len, +rule, msg}, rest}:
      keep(Config.level(cfg, Rules.group(rule), rule), F.Finding{path, line, col, len, rule, msg}, kept(cfg, rest))

# LAW: grading drops each finding whose rule is at off and attaches its
# rule's level to every other, in order
# BOLT-CFG-2
law graded_keeps:
  for +cfg: Config.Config
  for fs: List<&2, F.Finding>
  {Rules.graded(cfg, fs) == kept(cfg, fs) : List<&2, F.Graded>}

# LAW: a level word that is neither `off` nor `warn` is an error, so a typo
# makes a rule stricter, never silently off
# BOLT-CFG-3
law word_error:
  for +ww: String
  for h_off: {String.eq(ww, "off") == False{} : Bool}
  for h_warn: {String.eq(ww, "warn") == False{} : Bool}
  {Config.of_word(ww) == Config.Error{} : Config.Level}

# LAW: correctness defaults to error
# BOLT-CFG-5
law default_correctness:
  for +group: String
  for h: {group == "correctness" : String}
  {Config.default(group) == Config.Error{} : Config.Level}

# LAW: pedantic defaults to off
# BOLT-CFG-5
law default_pedantic:
  for +group: String
  for h: {group == "pedantic" : String}
  {Config.default(group) == Config.Off{} : Config.Level}

# LAW: every other group defaults to warn
# BOLT-CFG-5
law default_rest:
  for +group: String
  for h_c: {String.eq(group, "correctness") == False{} : Bool}
  for h_p: {String.eq(group, "pedantic") == False{} : Bool}
  {Config.default(group) == Config.Warn{} : Config.Level}

# LAW: an opt-in rule with no setting of its own is off, whatever its group
# says (with one, level_own gives it that setting)
# BOLT-CFG-6
law opt_in_off:
  for +sets: List<&2, Config.Set>
  for +group: String
  for +rule: String
  for h_opt: {Config.opt_in(rule) == True{} : Bool}
  for h_rule: {Config.set_level(sets, rule) == None{} : Maybe<&2, Config.Level>}
  {Config.level(Config.Config{sets}, group, rule) == Config.Off{} : Config.Level}
