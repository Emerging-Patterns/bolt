# The planner asks only what the World does not answer yet: of the questions
# it reads the World through, the ones still open are exactly those no reply
# holds, in the order they are read. So a question answered once is never
# asked again, and nothing is skipped that has no answer.
import Base
import ../src/lint/world.bend as W
import ../src/lint/plan.bend as Plan

# the questions the World does not answer, in order. Law vocabulary: bolt
# never calls it
def open(asks: List<&2, W.Ask>, +world: W.World) -> List<&2, W.Ask>:
  match asks:
    case Nil{}:
      Nil{}
    case Con{+a, rest}:
      +more = open(rest, world)
      Bool.pick(List<&2, W.Ask>, W.answered(world, a), more, a <> more)

# LAW: unanswered keeps a question exactly when the World holds no answer to
# it (W.answered), and keeps those in order
law unanswered_open:
  for asks: List<&2, W.Ask>
  for +world: W.World
  {Plan.unanswered(asks, world) == open(asks, world) : List<&2, W.Ask>}
