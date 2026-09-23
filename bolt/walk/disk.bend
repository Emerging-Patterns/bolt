# walk/disk: the real file system, through a foreign effect (dir.c, dir.js)
# that lists one directory: its names, one a line, a directory's name ending
# in "/"; one (cwd.c, cwd.js) that names the working directory; and Base's
# File, which tells a directory from a file.
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

# whether a first read failed as a directory's does (EISDIR, 21, in C and
# in node alike)
def is_dir.code(rr: Result<&1, &1, U32 & String, List<&2, U32>>) -> Bool:
  match rr:
    case Fail{e}:
      (code, _msg) = e
      U32.is_eq(code, 21)
    case Done{_bytes}:
      False{}

# the file closed, and what its first read said
def is_dir.got(got: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> IO(Bool):
  (file, rr) = got
  do IO<Bool>:
    File.close(file)
    return is_dir.code(rr)

# a path that opened: read one byte and see; one that did not is no directory
def is_dir.opened(rr: Result<&1, &1, U32 & String, File>) -> IO(Bool):
  match rr:
    case Fail{_e}:
      IO.pure(Bool, False{})
    case Done{file}:
      do IO<Bool>:
        got : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(file, 1)
        is_dir.got(got)

# whether a path is a directory: it opens, and reading it fails as a
# directory's read does. Base's File has no stat, and a directory opens for
# reading on both lanes.
def is_dir(path: String) -> IO(Bool):
  do IO<Bool>:
    r : Result<&1, &1, U32 & String, File> <- File.open(path, "r")
    is_dir.opened(r)

# the working directory, from the root; "" when it cannot be named
def walkdir.cwd() -> IO(String):
  import "./cwd.c"
  import "./cwd.js"

# the service's field takes a unit: the directory is asked for, not a constant
def cwd(_u: Unit) -> IO(String):
  walkdir.cwd()

# the real file system
def new() -> S.Walk:
  S.Walk{entries, is_dir, cwd}
