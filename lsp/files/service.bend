# files: an effect service: a file's text by path, and where Base lives.
import Base

# effect service: a file's text, and where Base is
type Files is Type:
  Files{read: String -> IO(Maybe<&2, String>), base_path: Unit -> IO(String)}

# None when the file cannot be read
def read(f: Files, path: String) -> IO(Maybe<&2, String>):
  Files{r, b} = f
  r(path)

# the path of Base, from a files service
def base_path(f: Files) -> IO(String):
  Files{r, b} = f
  b(Unit{})
