# A rule that has a limit is run at the one its file's bolt.bend sets
# (laws/ConfigLimitsResolve.bend), and at its own default when the config
# sets none. Tuning a run table to a config changes nothing else: the same
# rules in the same order, and a config with no limit leaves the table as it
# was, so a project that sets no limit is linted as before.
import Base
import ../src/config.bend as Config
import ../src/finding.bend as F
import ../src/role.bend as Role
import ../src/src.bend as Src
import ../src/rules.bend as Rules
import ../src/rules/style/reach.bend as Reach

# the slugs of a run table, in order
def slugs(rs: List<&2, Rules.Run>) -> List<&2, String>:
  match rs:
    case Nil{}:
      []
    case Con{Rules.Run{slug, _w}, rest}:
      slug <> slugs(rest)

# LAW: reach is tuned to the config's `reach_max`, and to the limit it had
# when the config sets none
law tune_reach:
  for cfg: Config.Config
  for max: U32
  {Rules.on.tune(cfg, Rules.WReach{max}) == Rules.WReach{Config.limit(cfg, "reach_max", max)} : Rules.Which}

# LAW: reach's entry runs the rule at the limit the entry carries
law run_reach_at_limit:
  for rr: Role.Role
  for ss: Src.Src
  for max: U32
  {Rules.on.run(Rules.WReach{max}, rr, ss) == Reach.check.role(rr, ss, max) : List<&2, F.Finding>}

# LAW: a tuned table runs the same rules in the same order
law tuned_keeps_slugs:
  for rs: List<&2, Rules.Run>
  for +cfg: Config.Config
  {slugs(Rules.on.tuned(rs, cfg)) == slugs(rs) : List<&2, String>}

# LAW: a config that sets no limit leaves every entry of a table as it was
law tuned_without_limits:
  for rs: List<&2, Rules.Run>
  for +sets: List<&2, Config.LevelSet>
  {Rules.on.tuned(rs, Config.Config{sets, Nil{}}) == rs : List<&2, Rules.Run>}
