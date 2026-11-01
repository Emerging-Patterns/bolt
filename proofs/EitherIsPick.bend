# proofs of laws/EitherIsPick.bend
import Base
import ../laws/EitherIsPick.bend as Laws

def Laws.either_is_pick(c, _a, _b):
  match c:
    case True{}:
      {==}
    case False{}:
      {==}
