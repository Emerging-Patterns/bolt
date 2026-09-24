# bolt/status: a run's exit status. A run that found errors exits 1, so a
# shell, the gate or an editor can tell without reading the output. `IO.die`
# is what sets the code; its message goes to stderr and the findings are
# already printed, so it is empty here (the runtime still ends it with a
# newline: one blank line on stderr is the whole cost).
import Base

# exit 1 when the run found errors, else fall through (exit 0)
def stop(bad: Bool) -> IO(Unit):  # noqa: L001 IO: exit status
  match bad:
    case True{}:
      IO.die(Unit, 1, "")
    case False{}:
      IO.pure(Unit, Unit{})
