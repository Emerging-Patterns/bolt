# proofs of laws/UniqKeepsFirstOccurrences.bend
import Base
import ../src/syntax/bind.bend as Bind
import ../src/lint/plan.bend as Plan
import ../laws/UniqKeepsFirstOccurrences.bend as Laws
import ./lemmas/BinderIndexIsContains.bend as M1

# uniq holds the paths met so far in the binder's index, each put in as it
# is met. The index of some names is List.contains over them
# (proofs/lemmas/BinderIndexIsContains.bend), and a name put in the index of
# a list is the index of the list with the name in front, so the walk over
# the index keeps what the law's walk over the list keeps.
law uq.fast:
  for ps: List<&2, String>
  for +seen: List<&2, String>
  {Plan.uniq.fast(ps, Bind.index(seen)) == Laws.uniq.first(ps, seen) : List<&2, String>}

def uq.fast(ps, seen):
  match ps:
    case Nil{}:
      {==}
    case Con{+p, +rest}:
      +fast = Plan.uniq.fast(rest, Bind.index(p <> seen))
      %Equal.sym(Bool, Bind.indexed(Bind.index(seen), p), List.contains(~String, ~String.eq, seen, p),
        M1.ic.indexed(seen, p)) :
        {Bool.pick(List<&2, String>, _, fast, p <> fast) == Laws.uniq.first(p <> rest, seen) : List<&2, String>}
      %Equal.sym(List<&2, String>, fast, Laws.uniq.first(rest, p <> seen), uq.fast(rest, p <> seen)) :
        {Bool.pick(List<&2, String>, List.contains(~String, ~String.eq, seen, p), _, p <> _)
          == Laws.uniq.first(p <> rest, seen) : List<&2, String>}
      {==}

def Laws.uniq_keeps_first(ps, seen):
  uq.fast(ps, seen)
