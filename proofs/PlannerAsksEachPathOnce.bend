# proofs of laws/PlannerAsksEachPathOnce.bend
import Base
import ../src/lint/world.bend as W
import ../src/lint/plan.bend as Plan
import ../laws/PlannerAsksEachPathOnce.bend as Laws

def Laws.entries_asked_in_order(_d, _rest):
  {==}

def Laws.texts_asked_in_order(_p, _rest):
  {==}

def Laws.config_by_name(_pp):
  {==}

def Laws.sources_drop_config(p, rest, e):
  %Equal.sym(Bool, Plan.is_config(p), True{}, e) :
    {Bool.pick(List<&2, String>, _, Plan.sources(rest), p <> Plan.sources(rest)) == Plan.sources(rest)
      : List<&2, String>}
  {==}

def Laws.sources_keep_files(p, rest, e):
  %Equal.sym(Bool, Plan.is_config(p), False{}, e) :
    {Bool.pick(List<&2, String>, _, Plan.sources(rest), p <> Plan.sources(rest)) == p <> Plan.sources(rest)
      : List<&2, String>}
  {==}
