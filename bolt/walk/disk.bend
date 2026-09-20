# walk/disk: the real file system, through a foreign effect (dir.c, dir.js)
# that lists one directory: its names, one a line, a directory's name ending
# in "/".
import Base
import ./service.bend as S

# every name directly in the directory, one a line
def walkdir.entries(dir: String) -> IO(String):
  import "./dir.c"
  import "./dir.js"

# the named lines: the text ends in a newline, so the last line is empty
def named(ls: List<&2, String>) -> List<&2, String>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{+l, t}:
      +more = named(t)
      Bool.pick(List<&2, String>, String.is_empty(l), more, l <> more)

# the service's field takes a plain path; quantities are part of its type
def entries(dir: String) -> IO(List<&2, String>):
  do IO<List<&2, String>>:
    text : String <- walkdir.entries(dir)
    return named(String.lines(text))

# the real file system
def new() -> S.Walk:
  S.Walk{entries}
