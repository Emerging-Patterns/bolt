# files: an effect service: a file's text by path, and where Base lives.
import Base

# effect service: a file's text, and where Base is
type Files is Type:
  Files{read: String -> IO(Maybe<&2, String>), base_path: Unit -> IO(String)}

# None when the file cannot be read
def read(ff: Files, path: String) -> IO(Maybe<&2, String>):
  Files{r, b} = ff
  r(path)

# the path of Base, from a files service
def base_path(ff: Files) -> IO(String):
  Files{r, b} = ff
  b(Unit{})

# every path read, in order (a missing file is a None)
def read_all(~ff: Files, paths: List<&2, String>) -> IO(List<&2, Maybe<&2, String>>):
  match paths:
    case Nil{}:
      IO.pure(List<&2, Maybe<&2, String>>, [])
    case Con{p, rest}:
      do IO<List<&2, Maybe<&2, String>>>:
        r : Maybe<&2, String> <- read(ff, p)
        more : List<&2, Maybe<&2, String>> <- read_all(~ff, rest)
        return r <> more
