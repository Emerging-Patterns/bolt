# bolt accepts `bolt check [files]`, `bolt format [--check] [files]`,
# `bolt lsp`, `bolt help [cmd]`, `--help` and `--`; an argv parse error exits
# 1, `help`, `--help` and `--version` exit 0, and `bolt` with no command
# prints the usage to stderr and exits 2. What shake answers for each argv is
# trusted in src/args.bend; the laws prove what bolt does with that answer.
#
# also rests on: laws/CliDashHelp.bend, laws/CliVersion.bend,
# laws/CliVersionExits.bend
import Base
import ../src/args.bend as Args
import shake@0.6.0.0/main.bend as Shake
import ./defs/CliWordKinds.bend as D1

# whether every word is plain
def all_plain(ws: List<&2, String>) -> Bool:
  match ws:
    case Nil{}:
      True{}
    case Con{+w, rest}:
      Bool.and(D1.plain_word(w), all_plain(rest))

# LAW: the files of a successful parse are the ones the selected command
# bound, read from that command's own Matched
law cli_files:
  for +m: Shake.Matched
  for +s: Shake.Matched
  for h: {Shake.at(m, Shake.path_of(m)) == Some{s} : Maybe<&2, Shake.Matched>}
  {Args.files(m) == Shake.get_all(s, "files") : List<&2, String>}

# LAW: every argv shake cannot parse, other than a request for usage, prints
# the error to stderr and exits 1
law cli_error_exits:
  for +av: List<&2, String>
  for +e: Shake.ParseErr
  for h: {Args.parse(av) == Fail{e} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  for h_help: {Shake.help_path(e) == None{} : Maybe<&2, List<&2, String>>}
  {Args.out(Args.parse(av)) == Args.Stop{Args.Err{}, Args.err_text(e), 1} : Args.Out}

# LAW: every argv that asks for usage prints the usage of its command path to
# stdout and exits 0
law cli_help_exits:
  for +av: List<&2, String>
  for +e: Shake.ParseErr
  for +ps: List<&2, String>
  for h: {Args.parse(av) == Fail{e} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  for h_help: {Shake.help_path(e) == Some{ps} : Maybe<&2, List<&2, String>>}
  {Args.out(Args.parse(av)) == Args.Stop{Args.Page{}, Args.help_text(ps), 0} : Args.Out}

# LAW: every other argv that parses and selects a command runs it over the
# files it bound, `format` told whether its `--check` was set
law cli_runs:
  for +av: List<&2, String>
  for +m: Shake.Matched
  for +c: String
  for +cs: List<&2, String>
  for h: {Args.parse(av) == Done{m} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  for h_ver: {Shake.on(m, "version") == False{} : Bool}
  for h_cmd: {Shake.path_of(m) == c <> cs : List<&2, String>}
  {Args.out(Args.parse(av))
    == Args.Go{Args.command.at(String.join(c <> cs, "/"), Args.checks(m)), Args.files(m)} : Args.Out}

# LAW: an argv that parses, selects no command and asks no version prints
# the usage to stderr and exits 2
law cli_no_command:
  for +av: List<&2, String>
  for +m: Shake.Matched
  for h: {Args.parse(av) == Done{m} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  for h_ver: {Shake.on(m, "version") == False{} : Bool}
  for h_cmd: {Shake.path_of(m) == [] : List<&2, String>}
  {Args.out(Args.parse(av)) == Args.Stop{Args.Err{}, Args.help_text([]), 2} : Args.Out}

# LAW: `bolt` alone prints the usage to stderr and exits 2. shake's answer,
# the premises: the empty line parses (SHAKE-PARSE-1), selects no command
# (SHAKE-PARSE-4) and sets no `--version` (SHAKE-GET-1)
law cli_bare:
  for +m: Shake.Matched
  for hp: {Args.parse([]) == Done{m} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  for hs: {Shake.path_of(m) == [] : List<&2, String>}
  for hv: {Shake.on(m, "version") == False{} : Bool}
  {Args.out(Args.parse([])) == Args.Stop{Args.Err{}, Args.help_text([]), 2} : Args.Out}

# LAW: `bolt check file..` lints the files, when no word is a flag, `--` or
# `help`. shake's answer, the premises: `check` selects its command
# (SHAKE-PARSE-4), the words bind its own `files` rest in order (SHAKE-TOK-3,
# SHAKE-PARSE-3), read back by `at` and `get_all` (SHAKE-GET-1,
# SHAKE-GET-2), and the root's `--version` is not set (SHAKE-GET-1)
law cli_check:
  for +fs: List<&2, String>
  for h: {all_plain(fs) == True{} : Bool}
  for +m: Shake.Matched
  for +s: Shake.Matched
  for hp: {Args.parse("check" <> fs) == Done{m} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  for hs: {Shake.path_of(m) == ["check"] : List<&2, String>}
  for ha: {Shake.at(m, Shake.path_of(m)) == Some{s} : Maybe<&2, Shake.Matched>}
  for hf: {Shake.get_all(s, "files") == fs : List<&2, String>}
  for hv: {Shake.on(m, "version") == False{} : Bool}
  {Args.out(Args.parse("check" <> fs)) == Args.Go{Args.CCheck{}, fs} : Args.Out}

# LAW: `bolt check -- word..` lints every word after the `--`. shake's
# answer, the premises: as cli_check's, the words bound after `--`
# (SHAKE-TOK-4)
law cli_check_raw:
  for +fs: List<&2, String>
  for +m: Shake.Matched
  for +s: Shake.Matched
  for hp: {Args.parse("check" <> "--" <> fs) == Done{m} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  for hs: {Shake.path_of(m) == ["check"] : List<&2, String>}
  for ha: {Shake.at(m, Shake.path_of(m)) == Some{s} : Maybe<&2, Shake.Matched>}
  for hf: {Shake.get_all(s, "files") == fs : List<&2, String>}
  for hv: {Shake.on(m, "version") == False{} : Bool}
  {Args.out(Args.parse("check" <> "--" <> fs)) == Args.Go{Args.CCheck{}, fs} : Args.Out}

# LAW: `bolt format file..` formats the files, when no word is a flag, `--`
# or `help` (none at all formats the tree). shake's answer, the premises: as
# cli_check's, `format` selected, and its `--check` not set (SHAKE-GET-1)
law cli_format:
  for +fs: List<&2, String>
  for h: {all_plain(fs) == True{} : Bool}
  for +m: Shake.Matched
  for +s: Shake.Matched
  for hp: {Args.parse("format" <> fs) == Done{m} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  for hs: {Shake.path_of(m) == ["format"] : List<&2, String>}
  for +ha: {Shake.at(m, Shake.path_of(m)) == Some{s} : Maybe<&2, Shake.Matched>}
  for hf: {Shake.get_all(s, "files") == fs : List<&2, String>}
  for hv: {Shake.on(m, "version") == False{} : Bool}
  for hc: {Shake.on(s, "check") == False{} : Bool}
  {Args.out(Args.parse("format" <> fs)) == Args.Go{Args.CFormat{False{}}, fs} : Args.Out}

# LAW: `bolt format --check file..` checks the files' format and is told
# so. shake's answer, the premises: as cli_format's, `--check` set on
# `format` (SHAKE-GET-1)
law cli_format_check:
  for +fs: List<&2, String>
  for h: {all_plain(fs) == True{} : Bool}
  for +m: Shake.Matched
  for +s: Shake.Matched
  for hp: {Args.parse("format" <> "--check" <> fs) == Done{m} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  for hs: {Shake.path_of(m) == ["format"] : List<&2, String>}
  for +ha: {Shake.at(m, Shake.path_of(m)) == Some{s} : Maybe<&2, Shake.Matched>}
  for hf: {Shake.get_all(s, "files") == fs : List<&2, String>}
  for hv: {Shake.on(m, "version") == False{} : Bool}
  for hc: {Shake.on(s, "check") == True{} : Bool}
  {Args.out(Args.parse("format" <> "--check" <> fs)) == Args.Go{Args.CFormat{True{}}, fs} : Args.Out}

# LAW: `bolt lsp` serves an editor. shake's answer, the premises: `lsp`
# selects its command (SHAKE-PARSE-4), which binds no files (SHAKE-GET-1),
# and the root's `--version` is not set (SHAKE-GET-1)
law cli_lsp:
  for +m: Shake.Matched
  for +s: Shake.Matched
  for hp: {Args.parse(["lsp"]) == Done{m} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  for hs: {Shake.path_of(m) == ["lsp"] : List<&2, String>}
  for ha: {Shake.at(m, Shake.path_of(m)) == Some{s} : Maybe<&2, Shake.Matched>}
  for hf: {Shake.get_all(s, "files") == [] : List<&2, String>}
  for hv: {Shake.on(m, "version") == False{} : Bool}
  {Args.out(Args.parse(["lsp"])) == Args.Go{Args.CLsp{}, []} : Args.Out}

# LAW: a plain word after `bolt lsp` is an error: stderr, exit 1. shake's
# answer, the premises: `lsp` has no positional, so the word fails the parse
# (SHAKE-PARSE-2) with an error that asks for no usage (SHAKE-ERR-1)
law cli_lsp_word:
  for +w: String
  for +ws: List<&2, String>
  for h: {D1.plain_word(w) == True{} : Bool}
  for +e: Shake.ParseErr
  for hp: {Args.parse("lsp" <> w <> ws) == Fail{e} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  for hh: {Shake.help_path(e) == None{} : Maybe<&2, List<&2, String>>}
  {Args.out(Args.parse("lsp" <> w <> ws)) == Args.Stop{Args.Err{}, Args.err_text(e), 1} : Args.Out}

# LAW: `bolt help cmd..` prints the usage of that command path to stdout and
# exits 0. shake's answer, the premise: `help` followed by a path of
# subcommands fails the parse as a request for usage of that path
# (SHAKE-PARSE-8, SHAKE-ERR-1)
law cli_help:
  for +ps: List<&2, String>
  for +e: Shake.ParseErr
  for hp: {Args.parse("help" <> ps) == Fail{e} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  for h: {Shake.help_path(e) == Some{ps} : Maybe<&2, List<&2, String>>}
  {Args.out(Args.parse("help" <> ps)) == Args.Stop{Args.Page{}, Args.help_text(ps), 0} : Args.Out}

# LAW: the files are a rest argument named `files` that need not be given,
# with no default and no fixed choices, whatever its help line: `bolt check`
# with no file lints the tree
law cli_files_optional:
  for +help: String
  {Args.spec.files(help) == Shake.rest("files", help, False{}, None{}, []) : Shake.Arg}

# bolt's program as shake is handed it, written out: the program `bolt` with
# its `--version` flag, and the commands `check`, `format`
# (with its `--check` flag) and `lsp`, each word and each help line.
# Law vocabulary: bolt never calls it
def cli.program() -> Shake.Cli:
  Shake.app("bolt", "A linter, checker and language server for Bend 2.", Some{Args.version()},
    [Shake.flag("version", None{}, Some{"version"}, "Print the version")],
    [Shake.sub("check", "Lint files", [Shake.rest("files", "Files to lint", False{}, None{}, [])], []),
     Shake.sub("format", "Format files",
       [Shake.flag("check", None{}, Some{"check"}, "List the files that would change and write nothing"),
        Shake.rest("files", "Files to format", False{}, None{}, [])], []),
     Shake.sub("lsp", "Serve an editor over stdio", [], [])])

# LAW: every argv is parsed against that program
law cli_parses_against_the_spec:
  for av: List<&2, String>
  {Args.parse(av) == Shake.parse(cli.program(), av) : Result<&2, &2, Shake.ParseErr, Shake.Matched>}

# LAW: and the usage of every command path is that program's
law cli_help_is_the_spec_s:
  for path: List<&2, String>
  {Args.help_text(path) == Shake.help(cli.program(), path) : String}

# LAW: with no command selected, the files are the ones the root bound under
# `files`
law cli_files_of_the_root:
  for +m: Shake.Matched
  {Args.files.at(None{}, m) == Shake.get_all(m, "files") : List<&2, String>}
