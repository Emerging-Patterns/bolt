# src/args: bolt's command line, parsed by shake. `bolt [lint] [file..]`,
# `bolt check file..`, `bolt lsp`, `bolt --version`. A rest positional at the root (and on
# `lint` / `check`) takes every leftover word, so `bolt a.bend b.bend` lints
# those files. `help` is shake's usage page; `--help` stays with the Bend
# runtime. A compiled binary does pass its arguments through; the runtime
# takes only its own out of the line (`--threads`, `--gpu`, `--gpu-build`,
# `--help`), wherever they stand, and `--` hands even those to the program.
# `out` is every decision the line makes, as data: what to print, where, and
# the exit code, or the subcommand to run and its files. main only does it.
# Only shake's interface (main.bend) is read here; what `parse` answers for a
# given argv is shake's guarantee (SPEC.md BOLT-TRUST-8), not bolt's.
import Base
import 0x085b03c84ca37125e38dddede7b91e55/main.bend as Shake
import ./version.bend as Ver
import ./build_rev.bend as Rev

# the line at the quantity the rest of bolt reads it at (IO.args gives each
# argument once)
def widen(ss: List<&1, String>) -> List<&2, String>:
  match ss:
    case Nil{}:
      Nil{}
    case Con{s, t}:
      s <> widen(t)

# bolt's command line
def argv() -> IO(List<&2, String>):  # noqa: L001 IO: reads argv
  do IO<List<&2, String>>:
    ss : List<&1, String> <- IO.args()
    return widen(ss)

# the files rest, optional, last among positionals
def spec.files(+help: String) -> Shake.Arg:
  Shake.rest("files", help, False{}, None{}, [])

# the release, with the short commit in parentheses when it is present
def version.at(+rel: String, +rev: String) -> String:
  Bool.pick(String, String.is_empty(rev), rel, rel ++ " (" ++ rev ++ ")")

# the release, and the short commit when the build has one
def version() -> String:
  version.at(Ver.text(), Rev.text())

# bolt's program spec
def spec() -> Shake.Cli:
  Shake.app("bolt", "A linter, checker and language server for Bend 2.", Some{version()},
    [Shake.flag("version", None{}, Some{"version"}, "Print the version"),
     spec.files("Files to lint")],
    [Shake.sub("lint", "Lint files", [spec.files("Files to lint")], []),
     Shake.sub("check", "Check files", [spec.files("Files to check")], []),
     Shake.sub("lsp", "Serve an editor over stdio", [], [])])

# argv against bolt's spec
def parse(av: List<&2, String>) -> Result<&2, &2, Shake.ParseErr, Shake.Matched>:
  Shake.parse(spec(), av)

# usage for a command path
def help_text(path: List<&2, String>) -> String:
  Shake.help(spec(), path)

# a parse error as the text the binary prints
def err_text(ee: Shake.ParseErr) -> String:
  Shake.err_text(spec(), ee)

# a subcommand
type Cmd is Data:
  CLint{}
  CCheck{}
  CLsp{}

# a subcommand by its name; the empty name (no subcommand) is `lint`
def command(+name: String) -> Cmd:
  Bool.pick(Cmd, String.eq(name, "check"), CCheck{},
    Bool.pick(Cmd, String.eq(name, "lsp"), CLsp{}, CLint{}))

# where a line that stops puts its text
type Stream is Data:
  Line{}
  Page{}
  Err{}

# what a parsed line does: print a text and exit with a code, or run a
# subcommand over files (which then exits as that command decides)
type Out is Data:
  Stop{to: Stream, text: String, code: U32}
  Go{cmd: Cmd, paths: List<&2, String>}

# the files the selected command bound: each command keeps its own
# bindings, so they are read from the Matched at the end of the selected
# path, which is the root's own when no subcommand was selected
def files.at(sel: Maybe<&2, Shake.Matched>, +mm: Shake.Matched) -> List<&2, String>:
  match sel:
    case Some{ss}:
      Shake.get_all(ss, "files")
    case None{}:
      Shake.get_all(mm, "files")

# the files a successful parse bound, to the command it selected
def files(+mm: Shake.Matched) -> List<&2, String>:
  files.at(Shake.at(mm, Shake.path_of(mm)), mm)

# a successful parse: the version, or the selected command and its files
def out.run(ask: Bool, +mm: Shake.Matched) -> Out:
  match ask:
    case True{}:
      Stop{Line{}, "bolt " ++ version(), 0}
    case False{}:
      Go{command(String.join(Shake.path_of(mm), "/")), files(mm)}

# a failed parse, given whether it asked for usage: that usage page, or the
# error
def out.fail.at(asked: Maybe<&2, List<&2, String>>, +ee: Shake.ParseErr) -> Out:
  match asked:
    case Some{path}:
      Stop{Page{}, help_text(path), 0}
    case None{}:
      Stop{Err{}, err_text(ee), 1}

# a failed parse: help text, or an error
def out.fail(+ee: Shake.ParseErr) -> Out:
  out.fail.at(Shake.help_path(ee), ee)

# a successful parse, read once for the version flag
def out.done(+mm: Shake.Matched) -> Out:
  out.run(Shake.on(mm, "version"), mm)

# what a parse result does
def out(rr: Result<&2, &2, Shake.ParseErr, Shake.Matched>) -> Out:
  match rr:
    case Fail{e}:
      out.fail(e)
    case Done{m}:
      out.done(m)
