# part of: laws/ConfigUnknownSettingsFound.bend,
# laws/SettingReportsUnknownNames.bend
import Base
import ../src/config.bend as Config
import ../src/codes.bend as Codes
import ../src/rules/laws/law.bend as Law

# Unknown names (laws/ConfigUnknownSettingsFound.bend). The specs below are strict folds over the code
# table, written apart from config.bend's lookups.

# whether some row of the table has the name as its slug. Law vocabulary, as
# are group_in and unknown_of.
def slug_in(rows: List<&2, Codes.Entry>, +name: String) -> Bool:
  match rows:
    case Nil{}:
      False{}
    case Con{Codes.Entry{+s, _id, _grp}, rest}:
      +more = slug_in(rest, name)
      Bool.or(String.eq(s, name), more)

# whether some row of the table has the name as its group
def group_in(rows: List<&2, Codes.Entry>, +name: String) -> Bool:
  match rows:
    case Nil{}:
      False{}
    case Con{Codes.Entry{_s, _id, +grp}, rest}:
      +more = group_in(rest, name)
      Bool.or(String.eq(grp, name), more)

# the settings, in order, whose name is neither the slug nor the group of any
# row of the code table
def unknown_of(ss: List<&2, Config.Setting>) -> List<&2, Config.Setting>:
  match ss:
    case Nil{}:
      Nil{}
    case Con{Config.Setting{+n, w, line}, rest}:
      +more = unknown_of(rest)
      Bool.pick(List<&2, Config.Setting>, Bool.or(slug_in(Codes.table(), n), group_in(Codes.table(), n)), more,
        Config.Setting{n, w, line} <> more)

# LAW: of a bolt.bend's settings, `unknown` holds exactly those whose name is
# neither the slug nor the group of any row of the code table, in file order,
# one each
law unknown_exact:
  for ss: List<&2, Config.Setting>
  {Config.unknown(ss) == unknown_of(ss) : List<&2, Config.Setting>}
