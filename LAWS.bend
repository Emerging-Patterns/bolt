# bolt: the laws main.bend needs. main parses the line and does what
# Args.out decides; these state that decision for every argv. The laws of
# everything under src/ are src/**/LAWS.bend.
import Base
import ./src/args.bend as Args
import ./src/version.bend as Ver
import ./src/build_rev.bend as Rev
import 0xba6940aab8a335b70bf79944bd9b53c4/main.bend as Shake

# The command line (BOLT-CLI). shake parses argv against bolt's spec
# (BOLT-TRUST-8), Args.out decides what the parse does, and main only does
# it (BOLT-TRUST-9): a Stop prints its text to its stream and exits with its
# code, and a Go runs its subcommand over the files, which then exits as that
# command decides (BOLT-OUT-4 for lint). The laws below quantify over every
# list of words after the command, and the exit laws over every argv. An argv
# here is the list IO.args hands the program: a compiled binary's runtime has
# already taken its own flags and the first `--` out of the command line, so
# at a shell `bolt -- -- -x.bend` is what reaches shake as `-- -x.bend`.

# a word bolt reads as a file after a command: neither `--` nor `help`, and
# not starting with `-` (a flag)
def plain_word(+ww: String) -> Bool:
  Bool.not(Bool.or(String.eq(ww, "--"), Bool.or(String.eq(ww, "help"), String.starts_with(ww, "-"))))

# a word bolt reads as a file with no command before it: a plain word that
# names no subcommand
def loose_word(+ww: String) -> Bool:
  Bool.and(plain_word(ww),
    Bool.not(Bool.or(String.eq("lint", ww), Bool.or(String.eq("check", ww), String.eq("lsp", ww)))))

# whether every word is plain
def all_plain(ws: List<&2, String>) -> Bool:
  match ws:
    case Nil{}:
      True{}
    case Con{+ww, rest}:
      Bool.and(plain_word(ww), all_plain(rest))

# whether every word is loose
def all_loose(ws: List<&2, String>) -> Bool:
  match ws:
    case Nil{}:
      True{}
    case Con{+ww, rest}:
      Bool.and(loose_word(ww), all_loose(rest))

# LAW: `bolt file..` lints the files, when no word is a flag, `--`, `help` or
# a subcommand's name (none at all lints the tree)
# BOLT-CLI-1
law cli_bare:
  for +fs: List<&2, String>
  for +h: {all_loose(fs) == True{} : Bool}
  {Args.out(Args.parse(fs)) == Args.Go{Args.CLint{}, fs} : Args.Out}

# LAW: `bolt -- word..` lints every word after the `--`, whatever it is
# BOLT-CLI-1
law cli_bare_raw:
  for +fs: List<&2, String>
  {Args.out(Args.parse("--" <> fs)) == Args.Go{Args.CLint{}, fs} : Args.Out}

# LAW: `bolt lint file..` lints the files, when no word is a flag, `--` or
# `help`
# BOLT-CLI-1
law cli_lint:
  for +fs: List<&2, String>
  for h: {all_plain(fs) == True{} : Bool}
  {Args.out(Args.parse("lint" <> fs)) == Args.Go{Args.CLint{}, fs} : Args.Out}

# LAW: `bolt lint -- word..` lints every word after the `--`
# BOLT-CLI-1
law cli_lint_raw:
  for +fs: List<&2, String>
  {Args.out(Args.parse("lint" <> "--" <> fs)) == Args.Go{Args.CLint{}, fs} : Args.Out}

# LAW: `bolt check file..` checks the files, when no word is a flag, `--` or
# `help`
# BOLT-CLI-1
law cli_check:
  for +fs: List<&2, String>
  for h: {all_plain(fs) == True{} : Bool}
  {Args.out(Args.parse("check" <> fs)) == Args.Go{Args.CCheck{}, fs} : Args.Out}

# LAW: `bolt check -- word..` checks every word after the `--`
# BOLT-CLI-1
law cli_check_raw:
  for +fs: List<&2, String>
  {Args.out(Args.parse("check" <> "--" <> fs)) == Args.Go{Args.CCheck{}, fs} : Args.Out}

# what `bolt lsp word..` does, the words plain: serve an editor when there
# are none; `lsp` takes no word, so the first is an unexpected argument
def lsp_out(ws: List<&2, String>) -> Args.Out:
  match ws:
    case Nil{}:
      Args.Go{Args.CLsp{}, []}
    case Con{ww, _rest}:
      Args.Stop{Args.Err{}, Args.err_text(Shake.Unexpected{ww}), 1}

# LAW: `bolt lsp` serves an editor, and a plain word after it is an error
# BOLT-CLI-1
law cli_lsp:
  for +ws: List<&2, String>
  for h: {all_plain(ws) == True{} : Bool}
  {Args.out(Args.parse("lsp" <> ws)) == lsp_out(ws) : Args.Out}

# LAW: `bolt help cmd..` prints the usage of that command path to stdout and
# exits 0, whatever the words
# BOLT-CLI-1
law cli_help:
  for +ps: List<&2, String>
  {Args.out(Args.parse("help" <> ps)) == Args.Stop{Args.Page{}, Args.help_text(ps), 0} : Args.Out}

# LAW: `bolt --version` prints bolt, then the release and the commit, and
# exits 0, with or without files after it
# BOLT-CLI-1
# BOLT-CLI-2
law cli_version:
  for +fs: List<&2, String>
  for +h: {all_loose(fs) == True{} : Bool}
  {Args.out(Args.parse("--version" <> fs))
    == Args.Stop{Args.Line{}, "bolt " ++ Args.version.at(Ver.text(), Rev.text()), 0} : Args.Out}

# whether a parse error is a request for usage
def asks_help(ee: Shake.ParseErr) -> Bool:
  match ee:
    case Shake.UnknownFlag{_ww}:
      False{}
    case Shake.Missing{_nn}:
      False{}
    case Shake.BadValue{_nn, _vv}:
      False{}
    case Shake.NeedHelp{_path}:
      True{}
    case Shake.Unexpected{_ww}:
      False{}

# LAW: every argv shake cannot parse, other than a request for usage, prints
# the error to stderr and exits 1
# BOLT-CLI-1
law cli_error_exits:
  for +av: List<&2, String>
  for +ee: Shake.ParseErr
  for h: {Args.parse(av) == Fail{ee} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  for h_help: {asks_help(ee) == False{} : Bool}
  {Args.out(Args.parse(av)) == Args.Stop{Args.Err{}, Args.err_text(ee), 1} : Args.Out}

# LAW: every argv that asks for usage prints the usage of its command path to
# stdout and exits 0
# BOLT-CLI-1
law cli_help_exits:
  for +av: List<&2, String>
  for +ps: List<&2, String>
  for h: {Args.parse(av) == Fail{Shake.NeedHelp{ps}} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  {Args.out(Args.parse(av)) == Args.Stop{Args.Page{}, Args.help_text(ps), 0} : Args.Out}

# LAW: every argv that parses with `--version` set prints bolt, then the
# release and the commit, and exits 0, whatever else it names
# BOLT-CLI-1
# BOLT-CLI-2
law cli_version_exits:
  for +av: List<&2, String>
  for +mm: Shake.Matched
  for h: {Args.parse(av) == Done{mm} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  for h_ver: {Shake.on(mm, "version") == True{} : Bool}
  {Args.out(Args.parse(av))
    == Args.Stop{Args.Line{}, "bolt " ++ Args.version.at(Ver.text(), Rev.text()), 0} : Args.Out}

# LAW: every other argv that parses runs the command it selects (`lint` when
# none) over the files it bound
# BOLT-CLI-1
law cli_runs:
  for +av: List<&2, String>
  for +mm: Shake.Matched
  for h: {Args.parse(av) == Done{mm} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  for h_ver: {Shake.on(mm, "version") == False{} : Bool}
  {Args.out(Args.parse(av))
    == Args.Go{Args.command(String.join(Shake.path_of(mm), "/")), Shake.get_all(mm, "files")} : Args.Out}

# LAW: a build with no commit prints the release alone
# BOLT-CLI-2
law version_release:
  for +rel: String
  for +rev: String
  for h: {String.is_empty(rev) == True{} : Bool}
  {Args.version.at(rel, rev) == rel : String}

# LAW: a build with a commit prints the release, then the commit in
# parentheses
# BOLT-CLI-2
law version_commit:
  for +rel: String
  for +rev: String
  for h: {String.is_empty(rev) == False{} : Bool}
  {Args.version.at(rel, rev) == rel ++ " (" ++ rev ++ ")" : String}
