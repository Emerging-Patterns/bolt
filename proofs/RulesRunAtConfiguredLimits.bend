# proofs of laws/RulesRunAtConfiguredLimits.bend
import Base
import ../src/config.bend as Config
import ../src/rules.bend as Rules
import ../src/rules/style/size.bend as Size
import ../laws/RulesRunAtConfiguredLimits.bend as Laws

def Laws.tune_reach(_cfg, _max):
  {==}

def Laws.run_reach_at_limit(_rr, _ss, _max):
  {==}

def Laws.tune_size(_cfg, _dim, _max):
  {==}

def Laws.run_size_at_limit(_rr, _ss, _dim, _max):
  {==}

def Laws.size_limit_names_known(dim):
  match dim:
    case Size.DArity{}:
      {==}
    case Size.DLength{}:
      {==}
    case Size.DDepth{}:
      {==}

def Laws.tuned_keeps_slugs(rs, cfg):
  match rs:
    case Nil{}:
      {==}
    case Con{Rules.Run{slug, w}, rest}:
      Equal.cong(List<&2, String>, List<&2, String>, z => slug <> z, Laws.slugs(Rules.on.tuned(rest, cfg)),
        Laws.slugs(rest), Laws.tuned_keeps_slugs(rest, cfg))

# a check tuned to a config with no limit is the check
law tune.none:
  for w: Rules.Which
  for sets: List<&2, Config.LevelSet>
  {Rules.on.tune(Config.Config{sets, Nil{}}, w) == w : Rules.Which}

def tune.none(w, _sets):
  match w:
    case Rules.WReach{max}:
      {==}
    case Rules.WSize{dim, max}:
      {==}
    case Rules.WDoc{}:
      {==}
    case Rules.WUnused{}:
      {==}
    case Rules.WHole{}:
      {==}
    case Rules.WSpace{}:
      {==}
    case Rules.WWrap{}:
      {==}
    case Rules.WPick{}:
      {==}
    case Rules.WSearch{}:
      {==}
    case Rules.WStrict{}:
      {==}
    case Rules.WEager{}:
      {==}
    case Rules.WTail{}:
      {==}
    case Rules.WConcat{}:
      {==}
    case Rules.WCont{}:
      {==}
    case Rules.WIndex{}:
      {==}
    case Rules.WRewalk{}:
      {==}
    case Rules.WThunk{}:
      {==}
    case Rules.WIdle{}:
      {==}
    case Rules.WFromrev{}:
      {==}
    case Rules.WPrefix{}:
      {==}
    case Rules.WEmpty{}:
      {==}
    case Rules.WBlank{}:
      {==}
    case Rules.WPut{}:
      {==}
    case Rules.WEscape{}:
      {==}
    case Rules.WStrings{}:
      {==}
    case Rules.WChars{}:
      {==}
    case Rules.WArms{}:
      {==}
    case Rules.WCover{}:
      {==}
    case Rules.WForeign{}:
      {==}
    case Rules.WFuel{}:
      {==}
    case Rules.WClosed{}:
      {==}
    case Rules.WTranscong{}:
      {==}

def Laws.tuned_without_limits(rs, sets):
  match rs:
    case Nil{}:
      {==}
    case Con{Rules.Run{+slug, +w}, +rest}:
      Equal.trans(List<&2, Rules.Run>,
        Rules.Run{slug, Rules.on.tune(Config.Config{sets, Nil{}}, w)} <> Rules.on.tuned(rest, Config.Config{sets,
          Nil{}}),
        Rules.Run{slug, w} <> Rules.on.tuned(rest, Config.Config{sets, Nil{}}),
        Rules.Run{slug, w} <> rest,
        Equal.cong(Rules.Which, List<&2, Rules.Run>,
          z => Rules.Run{slug, z} <> Rules.on.tuned(rest, Config.Config{sets, Nil{}}),
          Rules.on.tune(Config.Config{sets, Nil{}}, w), w, tune.none(w, sets)),
        Equal.cong(List<&2, Rules.Run>, List<&2, Rules.Run>, z => Rules.Run{slug, w} <> z,
          Rules.on.tuned(rest, Config.Config{sets, Nil{}}), rest, Laws.tuned_without_limits(rest, sets)))
