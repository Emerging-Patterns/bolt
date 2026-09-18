# check: the Reporter, an effect service: where a test's verdict goes.
import Base

# effect service: what to do with a passed and a failed check
type Reporter is Type:
  Reporter{pass: String -> IO(Unit), fail: String -> IO(Unit)}

# a check's outcome to the reporter
def report(ok: Bool, rep: Reporter, name: String) -> IO(Unit):
  match ok:
    case True{}:
      Reporter{p, f} = rep
      p(name)
    case False{}:
      Reporter{p, f} = rep
      f(name)
