# A bolt.bend sets a rule or a group to a level by a def whose body is one
# string: `def doc() -> String: "off"`, and a limit by one whose body is a
# number (laws/ConfigLimitsResolve.bend). Each such def is one setting, read
# in file order: its name, and its word, the string with its quotes dropped
# or the number as written. A config is
# those settings, each at the level its word names, in the same order, so the
# first setting of a name is the one that grades
# (laws/ConfigLevelsResolve.bend reads them from the front).
import Base
import ../src/config.bend as Config
import ../src/syntax/tree.bend as Tree
import ../src/syntax/bind.bend as Bind

# LAW: a token that opens and closes with a quote is read without them
law unquote_strips_quotes:
  for +tt: String
  for e: {Bool.and(String.starts_with(tt, "\""), String.ends_with(tt, "\"")) == True{} : Bool}
  {Config.unquote(tt) == String.take(String.drop(tt, 1n), (String.length(tt) - 2n : Nat)) : String}

# LAW: any other token is read as it is
law unquote_keeps_bare:
  for +tt: String
  for e: {Bool.and(String.starts_with(tt, "\""), String.ends_with(tt, "\"")) == False{} : Bool}
  {Config.unquote(tt) == tt : String}

# LAW: each setting gives its name the level its word names, in file order
law levels_in_order:
  for n: String
  for w: String
  for line: U32
  for rest: List<&2, Config.Setting>
  {Config.levels(Config.Setting{n, w, line} <> rest) == Config.LevelSet{n, Config.of_word(w)} <> Config.levels(rest)
    : List<&2, Config.LevelSet>}

# LAW: a bolt.bend's text is read as the levels of its settings, and its
# limits
law parse_reads_settings:
  for +text: String
  {Config.parse(text) == Config.Config{Config.levels(Config.settings(text)), Config.limits(text)} : Config.Config}

# LAW: a def's setting comes before the settings of the defs after it: the
# settings are in file order
law settings_in_file_order:
  for +kids: Tree.Node
  for body: Tree.Node
  for rest: Tree.Node
  {Config.settings.go(Tree.NCons{Tree.Stmt{Tree.SDef{}, kids, body}, rest})
    == List.append(&2, Config.Setting,
      Config.setting(Bind.declared(kids), Config.first_word(Tree.leaves(body)), Tree.line(kids)),
      Config.settings.go(rest)) : List<&2, Config.Setting>}
