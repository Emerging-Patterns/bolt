# Where the planner gathers paths that may repeat (the texts it asks for, the
# directories it grades, the bolt.bend files it reads), it keeps each once,
# where it first appears, so no text is asked for twice and no directory is
# graded twice.
import Base
import ../src/lint/plan.bend as Plan

# the paths that are none of those seen and none of those before them, in
# order. Law vocabulary: bolt never calls it
def uniq.first(ps: List<&2, String>, +seen: List<&2, String>) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{+p, rest}:
      +more = uniq.first(rest, p <> seen)
      Bool.pick(List<&2, String>, List.contains(~String, ~String.eq, seen, p), more, p <> more)

# LAW: uniq keeps a path exactly when it is none of the paths seen and none
# of the paths before it, and keeps those in order
law uniq_keeps_first:
  for ps: List<&2, String>
  for +seen: List<&2, String>
  {Plan.uniq(ps, seen) == uniq.first(ps, seen) : List<&2, String>}
