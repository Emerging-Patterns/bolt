# bolt/args: what the bolt script hands the binary through the environment,
# as a native Bend binary takes no arguments of its own: BOLT_CMD is the
# subcommand, BOLT_FILES the files, one a line.
import Base

# the non-empty strings
def nonempty(ss: List<&2, String>) -> List<&2, String>:
  match ss:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      +more = nonempty(t)
      Bool.pick(List<&2, String>, String.is_empty(h), more, h <> more)

# a variable's text; unset, ""
def text_of(r: Result<&1, &1, U32 & String, String>) -> String:
  match r:
    case Fail{e}:
      ""
    case Done{s}:
      s

# the files, one a line in BOLT_FILES
def files() -> IO(List<&2, String>):
  do IO<List<&2, String>>:
    r : Result<&1, &1, U32 & String, String> <- IO.get_env("BOLT_FILES")
    return nonempty(String.lines(text_of(r)))

# the subcommand in BOLT_CMD; unset, ""
def command() -> IO(String):
  do IO<String>:
    r : Result<&1, &1, U32 & String, String> <- IO.get_env("BOLT_CMD")
    return text_of(r)
