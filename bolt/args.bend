# bolt/args: bolt's command line, read from `IO.args()`: `bolt [lint]
# [file..]`, `bolt check file..`, `bolt lsp`. A compiled Bend binary does pass
# its arguments through, flags included; the runtime takes only its own out of
# the line (`--threads`, `--gpu`, `--gpu-build`, `--help`), wherever they
# stand, and `--` hands even those to the program. A word that is not a
# subcommand is a file, so `bolt x.bend` lints.
import Base

# the line at the quantity the rest of bolt reads it at (IO.args gives each
# argument once)
def widen(ss: List<&1, String>) -> List<&2, String>:
  match ss:
    case Nil{}:
      Nil{}
    case Con{s, t}:
      s <> widen(t)

# a word that names a subcommand
def is_command(+word: String) -> Bool:
  Bool.or(String.eq(word, "lint"), Bool.or(String.eq(word, "check"), String.eq(word, "lsp")))

# the subcommand the line opens with; none, ""
def command(av: List<&2, String>) -> String:
  match av:
    case Nil{}:
      ""
    case Con{+word, rest}:
      Bool.pick(String, is_command(word), word, "")

# the files: the line without the subcommand it opens with
def files(av: List<&2, String>) -> List<&2, String>:
  match av:
    case Nil{}:
      Nil{}
    case Con{+word, +rest}:
      Bool.pick(List<&2, String>, is_command(word), rest, word <> rest)

# bolt's command line
def argv() -> IO(List<&2, String>):
  do IO<List<&2, String>>:
    ss : List<&1, String> <- IO.args()
    return widen(ss)
