# a pick between lists equal branch by branch is equal
import Base

# a pick between lists equal branch by branch is equal
law unused.pick:
  for c: Bool
  for -a1: List<&2, U32>
  for -a2: List<&2, U32>
  for -b1: List<&2, U32>
  for -b2: List<&2, U32>
  for ea: {a1 == a2 : List<&2, U32>}
  for eb: {b1 == b2 : List<&2, U32>}
  {Bool.pick(List<&2, U32>, c, a1, b1) == Bool.pick(List<&2, U32>, c, a2, b2) : List<&2, U32>}

def unused.pick(c, _a1, _a2, _b1, _b2, ea, eb):
  match c:
    case True{}:
      ea
    case False{}:
      eb
