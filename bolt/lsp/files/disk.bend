# files/disk: the real file system. Reads bytes and decodes them itself, as a
# chunk may end inside a UTF-8 char.
import Base
import ./service.bend as S
import ../frame.bend as Frame

def slurp.end(file: File, acc: List<&2, U32>) -> IO(Maybe<&2, String>):
  do IO<Maybe<&2, String>>:
    File.close(file)
    return Some{Frame.decode(acc)}

def slurp.cut(bytes: List<&2, U32>, file: File, acc: List<&2, U32>,
  rest: File -> List<&2, U32> -> IO(Maybe<&2, String>)) -> IO(Maybe<&2, String>):
  match bytes:
    case Nil{}:
      slurp.end(file, acc)
    case Con{b, t}:
      rest(file, List.append(&2, U32, acc, b <> t))

def slurp.more(rr: Result<&1, &1, U32 & String, List<&2, U32>>, file: File, acc: List<&2, U32>,
  rest: File -> List<&2, U32> -> IO(Maybe<&2, String>)) -> IO(Maybe<&2, String>):
  match rr:
    case Fail{e}:
      slurp.end(file, acc)
    case Done{bytes}:
      slurp.cut(bytes, file, acc, rest)

def slurp.next(got: File & Result<&1, &1, U32 & String, List<&2, U32>>, acc: List<&2, U32>,
  rest: File -> List<&2, U32> -> IO(Maybe<&2, String>)) -> IO(Maybe<&2, String>):
  (file, r) = got
  slurp.more(r, file, acc, rest)

# the whole file, read in chunks until one is empty, or the fuel is
def slurp(fuel: Nat, file: File, acc: List<&2, U32>) -> IO(Maybe<&2, String>):
  match fuel:
    case 0n:
      slurp.end(file, acc)
    case 1n+f:
      do IO<Maybe<&2, String>>:
        got : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(file, 65536)
        slurp.next(got, acc, fl => a => slurp(f, fl, a))

def read.opened(rr: Result<&1, &1, U32 & String, File>) -> IO(Maybe<&2, String>):
  match rr:
    case Fail{e}:
      IO.pure(Maybe<&2, String>, None{})
    case Done{file}:
      slurp(U32.to_nat(100000), file, [])

# a file's text, or None when it cannot be opened
def read(path: String) -> IO(Maybe<&2, String>):
  do IO<Maybe<&2, String>>:
    r : Result<&1, &1, U32 & String, File> <- File.open(path, "r")
    read.opened(r)

def base_path.of(rr: Result<&1, &1, U32 & String, String>) -> IO(String):
  match rr:
    case Fail{e}:
      IO.pure(String, "")
    case Done{home}:
      IO.pure(String, home ++ "/.bend/current/bend2/base.bend")

# Base, where bend's installer puts it
def base_path(_u: Unit) -> IO(String):
  do IO<String>:
    r : Result<&1, &1, U32 & String, String> <- IO.get_env("HOME")
    base_path.of(r)

# the real file system
def new() -> S.Files:
  S.Files{read, base_path}
