# lazy: branches that do not run both ways. Bool.pick, Bool.and and Bool.or
# are ordinary defs, so every argument is evaluated before the call: a
# search written as `Bool.pick(T, hit, here, go(rest))` walks the whole list
# whatever `hit` says (measured native, 100 iterations over 100k cells: the
# hit at the head costs 0.10 s, the same as the hit at the end, while the
# forms here cost 0.00 s). A thunk `Unit -> T` is a value, so the branch
# that is not taken is never applied.
import Base

# `a` when c, else what rest gives: the early exit of a search
def stop(-A: Type, cc: Bool, aa: A, rest: Unit -> A) -> A:
  match cc:
    case True{}:
      aa
    case False{}:
      rest(Unit{})

# True when a, else what rest gives: `or` that stops at the first True
def or_else(aa: Bool, rest: Unit -> Bool) -> Bool:
  match aa:
    case True{}:
      True{}
    case False{}:
      rest(Unit{})

# what rest gives when a, else False: `and` that stops at the first False
def and_then(aa: Bool, rest: Unit -> Bool) -> Bool:
  match aa:
    case True{}:
      rest(Unit{})
    case False{}:
      False{}
