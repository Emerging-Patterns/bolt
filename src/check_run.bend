# check_run: an effect (CPU event loop only): `bolt check` performed.
# check.bend decides what a check prints and how it exits; this file runs
# bend on each file and does that.
import Base
import ./check.bend as Check
import ./lsp/checker/answer.bend as Checker
import ./lsp/checker/run.bend as Run

# every file checked, in order: what bend reported for each
def check_all(paths: List<&2, String>) -> IO(List<&2, Check.Run>):  # noqa: L001 IO driver
  match paths:
    case Nil{}:
      IO.pure(List<&2, Check.Run>, [])
    case Con{+path, rest}:
      do IO<List<&2, Check.Run>>:
        aa : Checker.Answer <- Run.check(path)
        more : List<&2, Check.Run> <- check_all(rest)
        return Check.run_of(path, aa) <> more

# the checker over the files given, exiting 1 when any of them had an error
def run(paths: List<&2, String>) -> IO(Unit):  # noqa: L001 IO driver
  do IO<Unit>:
    runs : List<&2, Check.Run> <- check_all(paths)
    Check.perform(Check.out(runs))
