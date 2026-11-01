# proofs of laws/ExitOnError.bend
import Base
import ../src/config.bend as Config
import ../src/finding.bend as F
import ../src/lint/plan.bend as Plan
import ../laws/ExitOnError.bend as Laws
import ../laws/defs/GradedFindingCounts.bend as D1
import ./lemmas/PlannerOutputOrder.bend as M1

# one graded finding onto whether any is an error
law lint.has_error.step:
  for ll: Config.Level
  for -a: Bool
  for -bb: Bool
  for e: {a == bb : Bool}
  {Bool.or(Config.is_error(ll), a) == Laws.any_error.one(ll, bb) : Bool}

def lint.has_error.step(ll, _a, _bb, e):
  match ll:
    case Config.Off{}:
      e
    case Config.Warn{}:
      e
    case Config.Error{}:
      {==}

# the planner sees an error exactly when the spec does
law lint.has_error:
  for gs: List<&2, F.Graded>
  {Plan.has_error(gs) == Laws.any_error(gs) : Bool}

def lint.has_error(gs):
  match gs:
    case Nil{}:
      {==}
    case Con{F.Graded{ll, _ff}, +tl}:
      lint.has_error.step(ll, Plan.has_error(tl), Laws.any_error(tl), lint.has_error(tl))

def Laws.exit_on_error(world):
  e = Equal.sym(List<&2, F.Graded>, Plan.final(world), D1.run_graded(world), M1.lint.final(world))
  %e : {Bool.pick(U32, Plan.has_error(_), 1, 0) == Bool.pick(U32, Laws.any_error(D1.run_graded(world)), 1, 0) : U32}
  h = Equal.sym(Bool, Plan.has_error(D1.run_graded(world)), Laws.any_error(D1.run_graded(world)),
    lint.has_error(D1.run_graded(world)))
  %h : {Bool.pick(U32, _, 1, 0) == Bool.pick(U32, Laws.any_error(D1.run_graded(world)), 1, 0) : U32}
  {==}
