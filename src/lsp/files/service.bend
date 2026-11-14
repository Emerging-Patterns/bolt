# files: an effect service: a file's text by path, where Base lives, the
# working directory a relative path is read against, and a directory's
# entries (a sub-directory's name ending in "/", as src/walk/ lists them).
import Base

# effect service: a file's text, where Base is, the working directory, and a
# directory's entries
type Files is Type:
  Files{read: String -> IO(Maybe<&2, String>), base_path: Unit -> IO(String), cwd: Unit -> IO(String),
    entries: String -> IO(List<&2, String>)}

# None when the file cannot be read
def read(f: Files, path: String) -> IO(Maybe<&2, String>):
  Files{r, _b, _c, _e} = f
  r(path)

# the path of Base, from a files service
def base_path(f: Files) -> IO(String):
  Files{_r, b, _c, _e} = f
  b(Unit{})

# the working directory, from the root; "" when it cannot be named
def cwd(f: Files) -> IO(String):  # noqa: L001 effect accessor
  Files{_r, _b, c, _e} = f
  c(Unit{})

# a directory's entries, none when it cannot be opened
def entries(f: Files, dir: String) -> IO(List<&2, String>):  # noqa: L001 effect accessor
  Files{_r, _b, _c, e} = f
  e(dir)

# every path read, in order (a missing file is a None)
def read_all(~ff: Files, paths: List<&2, String>) -> IO(List<&2, Maybe<&2, String>>):  # noqa: L001 effect accessor
  match paths:
    case Nil{}:
      IO.pure(List<&2, Maybe<&2, String>>, [])
    case Con{p, rest}:
      do IO<List<&2, Maybe<&2, String>>>:
        r : Maybe<&2, String> <- read(ff, p)
        more : List<&2, Maybe<&2, String>> <- read_all(~ff, rest)
        return r <> more
