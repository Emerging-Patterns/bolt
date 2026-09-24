# lsp/path: just enough path arithmetic to follow a relative import.
import Base

# a segment lands on the stack (reversed): `..` pops, `.` and `` do nothing
def push(+seg: String, +acc: List<&2, String>) -> List<&2, String>:
  Bool.pick(List<&2, String>, String.eq(seg, ".."), List.tail(&2, String, acc),
    Bool.pick(List<&2, String>, Bool.or(String.eq(seg, "."), String.is_empty(seg)), acc, seg <> acc))

# every segment pushed, in order
def norm(segs: List<&2, String>, acc: List<&2, String>) -> List<&2, String>:
  match segs:
    case Nil{}:
      acc
    case Con{s, t}:
      norm(t, push(s, acc))

# dir and rel as one absolute path, its `.` and `..` resolved
def join(dir: String, rel: String) -> String:
  "/" ++ String.join(List.reverse(&2, String, norm(String.split(dir ++ "/" ++ rel, '/'), [])), "/")

# the directory of a file's path
def dir(path: String) -> String:
  join(path, "..")
