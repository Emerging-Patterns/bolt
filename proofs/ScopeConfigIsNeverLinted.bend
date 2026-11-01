# proofs of laws/ScopeConfigIsNeverLinted.bend
import Base
import ../src/lint/plan.bend as Plan
import ../laws/ScopeConfigIsNeverLinted.bend as Laws

# one path onto a list with no bolt.bend, kept or dropped as the planner
# decides
law lint.no_config.pick:
  for bb: Bool
  for +p: String
  for +more: List<&2, String>
  for h: {Plan.is_config(p) == bb : Bool}
  for ih: {Laws.no_config(more) == True{} : Bool}
  {Laws.no_config(Bool.pick(List<&2, String>, bb, more, p <> more)) == True{} : Bool}

def lint.no_config.pick(bb, p, more, h, ih):
  match bb:
    case True{}:
      ih
    case False{}:
      e = Equal.sym(Bool, Plan.is_config(p), False{}, h)
      %e : {Bool.and(Bool.not(_), Laws.no_config(more)) == True{} : Bool}
      ih

# no source the planner keeps is a bolt.bend
law lint.no_config:
  for ps: List<&2, String>
  {Laws.no_config(Plan.sources(ps)) == True{} : Bool}

def lint.no_config(ps):
  match ps:
    case Nil{}:
      {==}
    case Con{+p, +tl}:
      lint.no_config.pick(Plan.is_config(p), p, Plan.sources(tl), {==}, lint.no_config(tl))

def Laws.no_config_linted(world):
  lint.no_config(Plan.files(world))
