# bolt/args: bolt's command line, parsed by shake. `bolt [lint] [file..]`,
# `bolt check file..`, `bolt lsp`. A rest positional at the root (and on
# `lint` / `check`) takes every leftover word, so `bolt a.bend b.bend` lints
# those files. `help` is shake's usage page; `--help` stays with the Bend
# runtime. A compiled binary does pass its arguments through; the runtime
# takes only its own out of the line (`--threads`, `--gpu`, `--gpu-build`,
# `--help`), wherever they stand, and `--` hands even those to the program.
import Base
import 0xba6940aab8a335b70bf79944bd9b53c4/main.bend as Shake

# the line at the quantity the rest of bolt reads it at (IO.args gives each
# argument once)
def widen(ss: List<&1, String>) -> List<&2, String>:
  match ss:
    case Nil{}:
      Nil{}
    case Con{s, t}:
      s <> widen(t)

# bolt's command line
def argv() -> IO(List<&2, String>):
  do IO<List<&2, String>>:
    ss : List<&1, String> <- IO.args()
    return widen(ss)

# the files rest, optional, last among positionals
def spec.files(+help: String) -> Shake.Arg:
  Shake.rest("files", help, False{}, None{}, [])

# bolt's program spec
def spec() -> Shake.Cli:
  Shake.app("bolt", "A linter, checker and language server for Bend 2.", None{},
    [spec.files("Files to lint")],
    [Shake.sub("lint", "Lint files", [spec.files("Files to lint")], []),
     Shake.sub("check", "Check files", [spec.files("Files to check")], []),
     Shake.sub("lsp", "Serve an editor over stdio", [], [])])

# argv against bolt's spec
def parse(av: List<&2, String>) -> Result<&2, &2, Shake.ParseErr, Shake.Matched>:
  Shake.parse(spec(), av)

# a parse as shake's one-line tag
def shown(av: List<&2, String>) -> String:
  Shake.show(parse(av))

# usage for a command path
def help_text(path: List<&2, String>) -> String:
  Shake.help(spec(), path)

# a parse error as the text the binary prints
def err_text(e: Shake.ParseErr) -> String:
  Shake.err_text(spec(), e)

# the selected command name; none, ""
def command.of(r: Result<&2, &2, Shake.ParseErr, Shake.Matched>) -> String:
  match r:
    case Done{m}:
      String.join(Shake.path_of(m), "/")
    case Fail{_e}:
      ""

# the subcommand the line opens with; none, ""
def command(av: List<&2, String>) -> String:
  command.of(parse(av))

# the files a successful parse bound; none on error
def files.of(r: Result<&2, &2, Shake.ParseErr, Shake.Matched>) -> List<&2, String>:
  match r:
    case Done{m}:
      Shake.get_all(m, "files")
    case Fail{_e}:
      []

# the files: leftover words under the rest name
def files(av: List<&2, String>) -> List<&2, String>:
  files.of(parse(av))
