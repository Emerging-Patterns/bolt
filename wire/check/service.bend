# check: the Reporter, an effect service: where a test's verdict goes.
import Base

type Reporter is Type:
  Reporter{pass: String -> IO(Unit), fail: String -> IO(Unit)}

def report(ok: Bool, rep: Reporter, name: String) -> IO(Unit):
  match ok:
    case True{}:
      Reporter{p, f} = rep
      p(name)
    case False{}:
      Reporter{p, f} = rep
      f(name)
