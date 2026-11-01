import Base
import ../src/rules/laws/law.bend as Law
import ../src/lint/world.bend as W
import ../src/lint/plan.bend as Plan

# The lint planner (lint/plan.bend) over its World (lint/world.bend). Every
# law below quantifies over every World: every list of paths the command line
# may name and every list of replies, whatever the interpreter would have
# answered. That the interpreter answers each question faithfully and prints
# the plan it is handed is trusted in src/lint.bend.

# whether a World answers every question. Law vocabulary: bolt never calls it.
def answered_all(+world: W.World, asks: List<&2, W.Ask>) -> Bool:
  match asks:
    case Nil{}:
      True{}
    case Con{a, rest}:
      +more = answered_all(world, rest)
      Bool.and(W.answered(world, a), more)

# LAW: the loop stops exactly when the plan has what it reads: nothing is
# wanted when, and only when, the World answers every question the planner
# reads it through (each listing the walk reads, each source and every
# bolt.bend candidate), so `plan` never runs on a question it would
# read as unanswered
law wants_tie:
  for +world: W.World
  {answered_all(world, Plan.looks(world)) == List.is_empty(&2, W.Ask, Plan.wants(world)) : Bool}
