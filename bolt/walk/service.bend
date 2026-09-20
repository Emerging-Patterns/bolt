# walk: an effect service (CPU event loop only): the names directly in a
# directory. A name that is itself a directory ends in "/"; "." and ".." are
# never in the list, and a directory that cannot be opened lists as empty.
# Order is the file system's; bolt/glob.bend sorts what it keeps.
import Base

# effect service: a directory's entry names, a directory marked by a `/`
type Walk is Type:
  Walk{entries: String -> IO(List<&2, String>)}

# a directory's entries, from a walk service
def entries(w: Walk, dir: String) -> IO(List<&2, String>):
  Walk{e} = w
  e(dir)
