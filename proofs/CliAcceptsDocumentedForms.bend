# proofs of laws/CliAcceptsDocumentedForms.bend
import Base
import ../src/args.bend as Args
import shake@0.6.0.0/main.bend as Shake
import ../laws/CliAcceptsDocumentedForms.bend as Laws
import ./lemmas/CliHelpExit.bend as M1

# The command line
# ---------------------------
# shake is read through its interface only: what `parse` answers for an argv
# is shake's guarantee (trusted in src/args.bend), and the laws naming an argv take it as
# their premises. So each proof rewrites the parse to the answer its premises
# give, then reads that answer back through Args.out, which is bolt's code.

def Laws.cli_files(mm, ss, h):
  e = Equal.sym(Maybe<&2, Shake.Matched>, Shake.at(mm, Shake.path_of(mm)), Some{ss}, h)
  %e : {Args.files.at(_, mm) == Shake.get_all(ss, "files") : List<&2, String>}
  {==}

def Laws.cli_error_exits(av, ee, h, h_help):
  e = Equal.sym(Result<&2, &2, Shake.ParseErr, Shake.Matched>, Args.parse(av), Fail{ee}, h)
  %e : {Args.out(_) == Args.Stop{Args.Err{}, Args.err_text(ee), 1} : Args.Out}
  q = Equal.sym(Maybe<&2, List<&2, String>>, Shake.help_path(ee), None{}, h_help)
  %q : {Args.out.fail.at(_, ee) == Args.Stop{Args.Err{}, Args.err_text(ee), 1} : Args.Out}
  {==}

def Laws.cli_runs(av, mm, h, h_ver):
  e = Equal.sym(Result<&2, &2, Shake.ParseErr, Shake.Matched>, Args.parse(av), Done{mm}, h)
  %e : {Args.out(_)
    == Args.Go{Args.command.at(String.join(Shake.path_of(mm), "/"), Args.checks(mm)), Args.files(mm)} : Args.Out}
  v = Equal.sym(Bool, Shake.on(mm, "version"), False{}, h_ver)
  %v : {Args.out.run(_, mm)
    == Args.Go{Args.command.at(String.join(Shake.path_of(mm), "/"), Args.checks(mm)), Args.files(mm)} : Args.Out}
  {==}

# a parse that selected the command at `path` and bound it the files runs
# that command over them: cli_runs, read with the premises shake gives
law cli.go:
  for +av: List<&2, String>
  for +mm: Shake.Matched
  for +ss: Shake.Matched
  for +path: List<&2, String>
  for +fs: List<&2, String>
  for hp: {Args.parse(av) == Done{mm} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  for hs: {Shake.path_of(mm) == path : List<&2, String>}
  for ha: {Shake.at(mm, Shake.path_of(mm)) == Some{ss} : Maybe<&2, Shake.Matched>}
  for hf: {Shake.get_all(ss, "files") == fs : List<&2, String>}
  for hv: {Shake.on(mm, "version") == False{} : Bool}
  {Args.out(Args.parse(av)) == Args.Go{Args.command.at(String.join(path, "/"), Args.checks(mm)), fs} : Args.Out}

def cli.go(av, mm, ss, _path, fs, hp, hs, ha, hf, hv):
  %hs : {Args.out(Args.parse(av)) == Args.Go{Args.command.at(String.join(_, "/"), Args.checks(mm)), fs} : Args.Out}
  ff = Equal.trans(List<&2, String>, Args.files(mm), Shake.get_all(ss, "files"), fs,
    Laws.cli_files(mm, ss, ha), hf)
  %ff : {Args.out(Args.parse(av))
    == Args.Go{Args.command.at(String.join(Shake.path_of(mm), "/"), Args.checks(mm)), _} : Args.Out}
  Laws.cli_runs(av, mm, hp, hv)

def Laws.cli_bare(fs, _h, mm, ss, hp, hs, ha, hf, hv):
  cli.go(fs, mm, ss, [], fs, hp, hs, ha, hf, hv)

def Laws.cli_bare_raw(fs, mm, ss, hp, hs, ha, hf, hv):
  cli.go("--" <> fs, mm, ss, [], fs, hp, hs, ha, hf, hv)

def Laws.cli_lint(fs, _h, mm, ss, hp, hs, ha, hf, hv):
  cli.go("lint" <> fs, mm, ss, ["lint"], fs, hp, hs, ha, hf, hv)

def Laws.cli_lint_raw(fs, mm, ss, hp, hs, ha, hf, hv):
  cli.go("lint" <> "--" <> fs, mm, ss, ["lint"], fs, hp, hs, ha, hf, hv)

# whether the selected command was given `--check` is read from its own
# Matched
law cli.checks:
  for +mm: Shake.Matched
  for +ss: Shake.Matched
  for -b: Bool
  for ha: {Shake.at(mm, Shake.path_of(mm)) == Some{ss} : Maybe<&2, Shake.Matched>}
  for hc: {Shake.on(ss, "check") == b : Bool}
  {Args.checks(mm) == b : Bool}

def cli.checks(mm, ss, b, ha, hc):
  a = Equal.sym(Maybe<&2, Shake.Matched>, Shake.at(mm, Shake.path_of(mm)), Some{ss}, ha)
  %a : {Args.checks.at(_) == b : Bool}
  hc

def Laws.cli_fmt(fs, _h, mm, ss, hp, hs, ha, hf, hv, hc):
  %cli.checks(mm, ss, False{}, ha, hc) : {Args.out(Args.parse("fmt" <> fs)) == Args.Go{Args.CFmt{_}, fs} : Args.Out}
  cli.go("fmt" <> fs, mm, ss, ["fmt"], fs, hp, hs, ha, hf, hv)

def Laws.cli_fmt_check(fs, _h, mm, ss, hp, hs, ha, hf, hv, hc):
  %cli.checks(mm, ss, True{}, ha, hc) :
    {Args.out(Args.parse("fmt" <> "--check" <> fs)) == Args.Go{Args.CFmt{_}, fs} : Args.Out}
  cli.go("fmt" <> "--check" <> fs, mm, ss, ["fmt"], fs, hp, hs, ha, hf, hv)

def Laws.cli_check(fs, _h, mm, ss, hp, hs, ha, hf, hv):
  cli.go("check" <> fs, mm, ss, ["check"], fs, hp, hs, ha, hf, hv)

def Laws.cli_check_raw(fs, mm, ss, hp, hs, ha, hf, hv):
  cli.go("check" <> "--" <> fs, mm, ss, ["check"], fs, hp, hs, ha, hf, hv)

def Laws.cli_lsp(mm, ss, hp, hs, ha, hf, hv):
  cli.go(["lsp"], mm, ss, ["lsp"], [], hp, hs, ha, hf, hv)

def Laws.cli_lsp_word(ww, ws, _h, ee, hp, hh):
  Laws.cli_error_exits("lsp" <> ww <> ws, ee, hp, hh)

def Laws.cli_files_optional(_help):
  {==}

def Laws.cli_parses_against_the_spec(_av):
  {==}

def Laws.cli_files_of_the_root(_mm):
  {==}

def Laws.cli_help_is_the_spec_s(_path):
  {==}

