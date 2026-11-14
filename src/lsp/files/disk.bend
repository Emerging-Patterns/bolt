# files/disk: the real file system. A file is read as one text of its size,
# so no read ends inside a UTF-8 char; anything past that size (a file that
# grew) is read on, a megabyte at a time. Each byte that is not UTF-8 reads
# as one char.
import Base
import ./service.bend as S
import ../../walk/disk.bend as WalkDisk

# the texts read, last first, as one text; the file closed
def whole.end(file: File, acc: List<&2, String>) -> IO(Maybe<&2, String>):
  do IO<Maybe<&2, String>>:
    File.close(file)
    return Some{String.join(List.reverse(&2, String, acc), "")}

# an empty read is the end; anything else is one more text
def whole.more(
  done: Bool,
  t: String,
  file: File,
  acc: List<&2, String>,
  rest: File -> List<&2, String> -> IO(Maybe<&2, String>)
) -> IO(Maybe<&2, String>):
  match done:
    case True{}:
      whole.end(file, acc)
    case False{}:
      rest(file, t <> acc)

# a read's text kept, or the end at a failed read
def whole.got(
  r: Result<&1, &1, U32 & String, String>,
  file: File,
  acc: List<&2, String>,
  rest: File -> List<&2, String> -> IO(Maybe<&2, String>)
) -> IO(Maybe<&2, String>):
  match r:
    case Fail{e}:
      whole.end(file, acc)
    case Done{+t}:
      whole.more(String.is_empty(t), t, file, acc, rest)

# a read and the file it leaves
def whole.next(
  got: File & Result<&1, &1, U32 & String, String>,
  acc: List<&2, String>,
  rest: File -> List<&2, String> -> IO(Maybe<&2, String>)
) -> IO(Maybe<&2, String>):
  (file, r) = got
  whole.got(r, file, acc, rest)

# what is left of the file, a megabyte a read, until a read is empty or the
# fuel is spent
def whole.rest(fuel: Nat, file: File, acc: List<&2, String>) -> IO(Maybe<&2, String>):
  match fuel:
    case 0n:
      whole.end(file, acc)
    case 1n+f:
      do IO<Maybe<&2, String>>:
        got : File & Result<&1, &1, U32 & String, String> <- File.read(file, 1048576)
        whole.next(got, acc, fl => a => whole.rest(f, fl, a))

# a size, or none known
def whole.size(r: Result<&1, &1, U32 & String, U32>) -> U32:
  match r:
    case Fail{e}:
      0
    case Done{n}:
      n

# the file read as one text of its size, then whatever more it holds
def whole.sized(got: File & Result<&1, &1, U32 & String, U32>) -> IO(Maybe<&2, String>):
  (file, r) = got
  do IO<Maybe<&2, String>>:
    first : File & Result<&1, &1, U32 & String, String> <- File.read(file, whole.size(r))
    whole.next(first, [], fl => a => whole.rest(100000n, fl, a))

def read.opened(r: Result<&1, &1, U32 & String, File>) -> IO(Maybe<&2, String>):
  match r:
    case Fail{e}:
      IO.pure(Maybe<&2, String>, None{})
    case Done{file}:
      do IO<Maybe<&2, String>>:
        got : File & Result<&1, &1, U32 & String, U32> <- File.size(file)
        whole.sized(got)

# a file's text, or None when it cannot be opened
def read(path: String) -> IO(Maybe<&2, String>):
  do IO<Maybe<&2, String>>:
    r : Result<&1, &1, U32 & String, File> <- File.open(path, "r")
    read.opened(r)

def base_path.of(r: Result<&1, &1, U32 & String, String>) -> IO(String):
  match r:
    case Fail{e}:
      IO.pure(String, "")
    case Done{home}:
      IO.pure(String, home ++ "/.bend/current/bend2/base.bend")

# Base, where bend's installer puts it
def base_path(_u: Unit) -> IO(String):
  do IO<String>:
    r : Result<&1, &1, U32 & String, String> <- IO.get_env("HOME")
    base_path.of(r)

# the working directory, as the lint's walk names it
def cwd(_u: Unit) -> IO(String):
  WalkDisk.cwd()

# a directory's entries, as the lint's walk lists them
def entries(dir: String) -> IO(List<&2, String>):
  WalkDisk.entries(dir)

# the real file system
def new() -> S.Files:  # noqa: L001 effect record
  S.Files{read, base_path, cwd, entries}
