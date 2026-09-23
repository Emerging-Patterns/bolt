# walk: an effect service (CPU event loop only): the names directly in a
# directory, and the working directory relative paths are named from. A name
# that is itself a directory ends in "/"; "." and ".." are never in the list,
# and a directory that cannot be opened lists as empty.
# Order is the file system's; the lint planner (bolt/lint/plan.bend) sorts
# what it keeps.
import Base

# effect service: a directory's entry names, a directory marked by a `/`,
# and the working directory, from the root ("" when it cannot be named)
type Walk is Type:
  Walk{entries: String -> IO(List<&2, String>), cwd: Unit -> IO(String)}

# a directory's entries, from a walk service
def entries(ww: Walk, dir: String) -> IO(List<&2, String>):
  Walk{e, _c} = ww
  e(dir)

# the working directory, from a walk service
def cwd(ww: Walk) -> IO(String):
  Walk{_e, c} = ww
  c(Unit{})
