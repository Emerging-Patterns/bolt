# proofs of laws/LazyMatchesEagerCombinators.bend
import Base
import ../laws/LazyMatchesEagerCombinators.bend as Laws

def Laws.stop_is_pick(c, _a, _b):
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.or_else_is_or(a, _b):
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.and_then_is_and(a, _b):
  match a:
    case True{}:
      {==}
    case False{}:
      {==}
