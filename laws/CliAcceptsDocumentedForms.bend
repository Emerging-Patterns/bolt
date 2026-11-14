# bolt accepts `bolt [lint] [files]`, `bolt check files`, `bolt fmt [--check]
# [files]`, `bolt lsp`, `bolt help [cmd]`, `--help` and `--`; an argv parse error exits 1, and `help`,
# `--help` and `--version` exit 0. What shake answers for each argv is
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
    case Con{+ww, rest}:
      Bool.and(D1.plain_word(ww), all_plain(rest))

# LAW: the files of a successful parse are the ones the selected command
# bound, read from that command's own Matched
law cli_files:
  for +mm: Shake.Matched
  for +ss: Shake.Matched
  for h: {Shake.at(mm, Shake.path_of(mm)) == Some{ss} : Maybe<&2, Shake.Matched>}
  {Args.files(mm) == Shake.get_all(ss, "files") : List<&2, String>}

# LAW: every argv shake cannot parse, other than a request for usage, prints
# the error to stderr and exits 1
law cli_error_exits:
  for +av: List<&2, String>
  for +ee: Shake.ParseErr
  for h: {Args.parse(av) == Fail{ee} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  for h_help: {Shake.help_path(ee) == None{} : Maybe<&2, List<&2, String>>}
  {Args.out(Args.parse(av)) == Args.Stop{Args.Err{}, Args.err_text(ee), 1} : Args.Out}

# LAW: every argv that asks for usage prints the usage of its command path to
# stdout and exits 0
law cli_help_exits:
  for +av: List<&2, String>
  for +ee: Shake.ParseErr
  for +ps: List<&2, String>
  for h: {Args.parse(av) == Fail{ee} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  for h_help: {Shake.help_path(ee) == Some{ps} : Maybe<&2, List<&2, String>>}
  {Args.out(Args.parse(av)) == Args.Stop{Args.Page{}, Args.help_text(ps), 0} : Args.Out}

# LAW: every other argv that parses runs the command it selects (`lint` when
# none) over the files that command bound, `fmt` told whether its `--check`
# was set
law cli_runs:
  for +av: List<&2, String>
  for +mm: Shake.Matched
  for h: {Args.parse(av) == Done{mm} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  for h_ver: {Shake.on(mm, "version") == False{} : Bool}
  {Args.out(Args.parse(av))
    == Args.Go{Args.command.at(String.join(Shake.path_of(mm), "/"), Args.checks(mm)), Args.files(mm)} : Args.Out}

# LAW: `bolt file..` lints the files, when no word is a flag, `--`, `help` or
# a subcommand's name (none at all lints the tree). shake's answer, the
# premises: the words select no command (SHAKE-PARSE-4) and bind the root's
# `files` rest in order (SHAKE-TOK-3, SHAKE-PARSE-3), read back by `at` and
# `get_all` (SHAKE-GET-1, SHAKE-GET-2), and no `--version` is set
# (SHAKE-GET-1)
law cli_bare:
  for +fs: List<&2, String>
  for h: {D1.all_loose(fs) == True{} : Bool}
  for +mm: Shake.Matched
  for +ss: Shake.Matched
  for hp: {Args.parse(fs) == Done{mm} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  for hs: {Shake.path_of(mm) == [] : List<&2, String>}
  for ha: {Shake.at(mm, Shake.path_of(mm)) == Some{ss} : Maybe<&2, Shake.Matched>}
  for hf: {Shake.get_all(ss, "files") == fs : List<&2, String>}
  for hv: {Shake.on(mm, "version") == False{} : Bool}
  {Args.out(Args.parse(fs)) == Args.Go{Args.CLint{}, fs} : Args.Out}

# LAW: `bolt -- word..` lints every word after the `--`, whatever it is.
# shake's answer, the premises: after `--` every word binds the root's
# `files` rest (SHAKE-TOK-4, SHAKE-PARSE-3) and selects no command
# (SHAKE-PARSE-4), read back by `at` and `get_all` (SHAKE-GET-1,
# SHAKE-GET-2), and no `--version` is set (SHAKE-GET-1)
law cli_bare_raw:
  for +fs: List<&2, String>
  for +mm: Shake.Matched
  for +ss: Shake.Matched
  for hp: {Args.parse("--" <> fs) == Done{mm} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  for hs: {Shake.path_of(mm) == [] : List<&2, String>}
  for ha: {Shake.at(mm, Shake.path_of(mm)) == Some{ss} : Maybe<&2, Shake.Matched>}
  for hf: {Shake.get_all(ss, "files") == fs : List<&2, String>}
  for hv: {Shake.on(mm, "version") == False{} : Bool}
  {Args.out(Args.parse("--" <> fs)) == Args.Go{Args.CLint{}, fs} : Args.Out}

# LAW: `bolt lint file..` lints the files, when no word is a flag, `--` or
# `help`. shake's answer, the premises: `lint` selects its command
# (SHAKE-PARSE-4), the words bind its own `files` rest in order (SHAKE-TOK-3,
# SHAKE-PARSE-3), read back by `at` and `get_all` (SHAKE-GET-1,
# SHAKE-GET-2), and the root's `--version` is not set (SHAKE-GET-1)
law cli_lint:
  for +fs: List<&2, String>
  for h: {all_plain(fs) == True{} : Bool}
  for +mm: Shake.Matched
  for +ss: Shake.Matched
  for hp: {Args.parse("lint" <> fs) == Done{mm} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  for hs: {Shake.path_of(mm) == ["lint"] : List<&2, String>}
  for ha: {Shake.at(mm, Shake.path_of(mm)) == Some{ss} : Maybe<&2, Shake.Matched>}
  for hf: {Shake.get_all(ss, "files") == fs : List<&2, String>}
  for hv: {Shake.on(mm, "version") == False{} : Bool}
  {Args.out(Args.parse("lint" <> fs)) == Args.Go{Args.CLint{}, fs} : Args.Out}

# LAW: `bolt lint -- word..` lints every word after the `--`. shake's
# answer, the premises: as cli_lint's, the words bound after `--`
# (SHAKE-TOK-4)
law cli_lint_raw:
  for +fs: List<&2, String>
  for +mm: Shake.Matched
  for +ss: Shake.Matched
  for hp: {Args.parse("lint" <> "--" <> fs) == Done{mm} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  for hs: {Shake.path_of(mm) == ["lint"] : List<&2, String>}
  for ha: {Shake.at(mm, Shake.path_of(mm)) == Some{ss} : Maybe<&2, Shake.Matched>}
  for hf: {Shake.get_all(ss, "files") == fs : List<&2, String>}
  for hv: {Shake.on(mm, "version") == False{} : Bool}
  {Args.out(Args.parse("lint" <> "--" <> fs)) == Args.Go{Args.CLint{}, fs} : Args.Out}

# LAW: `bolt check file..` checks the files, when no word is a flag, `--` or
# `help`. shake's answer, the premises: as cli_lint's, `check` selected
law cli_check:
  for +fs: List<&2, String>
  for h: {all_plain(fs) == True{} : Bool}
  for +mm: Shake.Matched
  for +ss: Shake.Matched
  for hp: {Args.parse("check" <> fs) == Done{mm} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  for hs: {Shake.path_of(mm) == ["check"] : List<&2, String>}
  for ha: {Shake.at(mm, Shake.path_of(mm)) == Some{ss} : Maybe<&2, Shake.Matched>}
  for hf: {Shake.get_all(ss, "files") == fs : List<&2, String>}
  for hv: {Shake.on(mm, "version") == False{} : Bool}
  {Args.out(Args.parse("check" <> fs)) == Args.Go{Args.CCheck{}, fs} : Args.Out}

# LAW: `bolt check -- word..` checks every word after the `--`. shake's
# answer, the premises: as cli_check's, the words bound after `--`
# (SHAKE-TOK-4)
law cli_check_raw:
  for +fs: List<&2, String>
  for +mm: Shake.Matched
  for +ss: Shake.Matched
  for hp: {Args.parse("check" <> "--" <> fs) == Done{mm} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  for hs: {Shake.path_of(mm) == ["check"] : List<&2, String>}
  for ha: {Shake.at(mm, Shake.path_of(mm)) == Some{ss} : Maybe<&2, Shake.Matched>}
  for hf: {Shake.get_all(ss, "files") == fs : List<&2, String>}
  for hv: {Shake.on(mm, "version") == False{} : Bool}
  {Args.out(Args.parse("check" <> "--" <> fs)) == Args.Go{Args.CCheck{}, fs} : Args.Out}

# LAW: `bolt fmt file..` formats the files, when no word is a flag, `--` or
# `help` (none at all formats the tree). shake's answer, the premises: as
# cli_lint's, `fmt` selected, and its `--check` not set (SHAKE-GET-1)
law cli_fmt:
  for +fs: List<&2, String>
  for h: {all_plain(fs) == True{} : Bool}
  for +mm: Shake.Matched
  for +ss: Shake.Matched
  for hp: {Args.parse("fmt" <> fs) == Done{mm} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  for hs: {Shake.path_of(mm) == ["fmt"] : List<&2, String>}
  for +ha: {Shake.at(mm, Shake.path_of(mm)) == Some{ss} : Maybe<&2, Shake.Matched>}
  for hf: {Shake.get_all(ss, "files") == fs : List<&2, String>}
  for hv: {Shake.on(mm, "version") == False{} : Bool}
  for hc: {Shake.on(ss, "check") == False{} : Bool}
  {Args.out(Args.parse("fmt" <> fs)) == Args.Go{Args.CFmt{False{}}, fs} : Args.Out}

# LAW: `bolt fmt --check file..` checks the files' format and is told so.
# shake's answer, the premises: as cli_fmt's, `--check` set on `fmt`
# (SHAKE-GET-1)
law cli_fmt_check:
  for +fs: List<&2, String>
  for h: {all_plain(fs) == True{} : Bool}
  for +mm: Shake.Matched
  for +ss: Shake.Matched
  for hp: {Args.parse("fmt" <> "--check" <> fs) == Done{mm} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  for hs: {Shake.path_of(mm) == ["fmt"] : List<&2, String>}
  for +ha: {Shake.at(mm, Shake.path_of(mm)) == Some{ss} : Maybe<&2, Shake.Matched>}
  for hf: {Shake.get_all(ss, "files") == fs : List<&2, String>}
  for hv: {Shake.on(mm, "version") == False{} : Bool}
  for hc: {Shake.on(ss, "check") == True{} : Bool}
  {Args.out(Args.parse("fmt" <> "--check" <> fs)) == Args.Go{Args.CFmt{True{}}, fs} : Args.Out}

# LAW: `bolt lsp` serves an editor. shake's answer, the premises: `lsp`
# selects its command (SHAKE-PARSE-4), which binds no files (SHAKE-GET-1),
# and the root's `--version` is not set (SHAKE-GET-1)
law cli_lsp:
  for +mm: Shake.Matched
  for +ss: Shake.Matched
  for hp: {Args.parse(["lsp"]) == Done{mm} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  for hs: {Shake.path_of(mm) == ["lsp"] : List<&2, String>}
  for ha: {Shake.at(mm, Shake.path_of(mm)) == Some{ss} : Maybe<&2, Shake.Matched>}
  for hf: {Shake.get_all(ss, "files") == [] : List<&2, String>}
  for hv: {Shake.on(mm, "version") == False{} : Bool}
  {Args.out(Args.parse(["lsp"])) == Args.Go{Args.CLsp{}, []} : Args.Out}

# LAW: a plain word after `bolt lsp` is an error: stderr, exit 1. shake's
# answer, the premises: `lsp` has no positional, so the word fails the parse
# (SHAKE-PARSE-2) with an error that asks for no usage (SHAKE-ERR-1)
law cli_lsp_word:
  for +ww: String
  for +ws: List<&2, String>
  for h: {D1.plain_word(ww) == True{} : Bool}
  for +ee: Shake.ParseErr
  for hp: {Args.parse("lsp" <> ww <> ws) == Fail{ee} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  for hh: {Shake.help_path(ee) == None{} : Maybe<&2, List<&2, String>>}
  {Args.out(Args.parse("lsp" <> ww <> ws)) == Args.Stop{Args.Err{}, Args.err_text(ee), 1} : Args.Out}

# LAW: `bolt help cmd..` prints the usage of that command path to stdout and
# exits 0. shake's answer, the premise: `help` followed by a path of
# subcommands fails the parse as a request for usage of that path
# (SHAKE-PARSE-8, SHAKE-ERR-1)
law cli_help:
  for +ps: List<&2, String>
  for +ee: Shake.ParseErr
  for hp: {Args.parse("help" <> ps) == Fail{ee} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  for hh: {Shake.help_path(ee) == Some{ps} : Maybe<&2, List<&2, String>>}
  {Args.out(Args.parse("help" <> ps)) == Args.Stop{Args.Page{}, Args.help_text(ps), 0} : Args.Out}

# LAW: the files are a rest argument named `files` that need not be given,
# with no default and no fixed choices, whatever its help line: `bolt` with
# no file lints the tree
law cli_files_optional:
  for +help: String
  {Args.spec.files(help) == Shake.rest("files", help, False{}, None{}, []) : Shake.Arg}

# bolt's program as shake is handed it, written out: the program `bolt` with
# its `--version` flag and its files, and the commands `lint`, `check` and
# `lsp`, each word and each help line. Law vocabulary: bolt never calls it
def cli.program() -> Shake.Cli:
  Shake.app("bolt", "A linter, checker and language server for Bend 2.", Some{Args.version()},
    [Shake.flag("version", None{}, Some{"version"}, "Print the version"),
     Shake.rest("files", "Files to lint", False{}, None{}, [])],
    [Shake.sub("lint", "Lint files", [Shake.rest("files", "Files to lint", False{}, None{}, [])], []),
     Shake.sub("check", "Check files", [Shake.rest("files", "Files to check", False{}, None{}, [])], []),
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
  for +mm: Shake.Matched
  {Args.files.at(None{}, mm) == Shake.get_all(mm, "files") : List<&2, String>}
