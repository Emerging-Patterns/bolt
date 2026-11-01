# proofs of laws/LspCheckerNeverRunsMain.bend
import Base
import ../src/lsp/checker/argv.bend as Argv
import ../src/paths.bend as Paths
import ../laws/LspCheckerNeverRunsMain.bend as Laws

# the checker
# -----------

def Laws.check_only(_path):
  {==}

# a run's flag, or the check-only flag when there is no run
def nav.flag_or(mm: Maybe<&2, Argv.Run>) -> String:
  match mm:
    case None{}:
      "--check-only"
    case Some{rr}:
      Argv.flag(rr)

# whichever way the followup's condition goes, a run it gives checks only
law nav.picked_check_only:
  for cc: Bool
  for +path: String
  for rr: Argv.Run
  for h: {Bool.pick(Maybe<&2, Argv.Run>, cc, Some{Argv.run_of(path)}, None{}) == Some{rr} : Maybe<&2, Argv.Run>}
  {Argv.flag(rr) == "--check-only" : String}

def nav.picked_check_only(cc, path, rr, h):
  match cc:
    case False{}:
      Equal.sym(String, "--check-only", Argv.flag(rr),
        Equal.cong(Maybe<&2, Argv.Run>, String, nav.flag_or, None{}, Some{rr}, h))
    case True{}:
      Equal.sym(String, "--check-only", Argv.flag(rr),
        Equal.cong(Maybe<&2, Argv.Run>, String, nav.flag_or, Some{Argv.run_of(path)}, Some{rr}, h))

def Laws.followup_check_only(ds, path, rr, h):
  nav.picked_check_only(Bool.and(Argv.only_todos(ds), Paths.is_laws(path)), Argv.proof_path(path), rr, h)
