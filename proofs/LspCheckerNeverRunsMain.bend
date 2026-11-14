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
def nav.flag_or(m: Maybe<&2, Argv.Run>) -> String:
  match m:
    case None{}:
      "--check-only"
    case Some{r}:
      Argv.flag(r)

# whichever way the followup's condition goes, a run it gives checks only
law nav.picked_check_only:
  for c: Bool
  for +path: String
  for r: Argv.Run
  for h: {Bool.pick(Maybe<&2, Argv.Run>, c, Some{Argv.run_of(path)}, None{}) == Some{r} : Maybe<&2, Argv.Run>}
  {Argv.flag(r) == "--check-only" : String}

def nav.picked_check_only(c, path, r, h):
  match c:
    case False{}:
      Equal.sym(String, "--check-only", Argv.flag(r),
        Equal.cong(Maybe<&2, Argv.Run>, String, nav.flag_or, None{}, Some{r}, h))
    case True{}:
      Equal.sym(String, "--check-only", Argv.flag(r),
        Equal.cong(Maybe<&2, Argv.Run>, String, nav.flag_or, Some{Argv.run_of(path)}, Some{r}, h))

def Laws.followup_check_only(ds, path, r, h):
  nav.picked_check_only(Bool.and(Argv.only_todos(ds), Paths.is_laws(path)), Argv.proof_path(path), r, h)

def Laws.proof_beside_its_laws(_path):
  {==}
