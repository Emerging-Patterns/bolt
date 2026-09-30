# checker/service: pure (GPU-safe): the checker as a value a caller is
# given. The server takes one, so a proof of the server does not import
# checker/run.bend.
import Base
import ./answer.bend as S

# a checker's run on one path
type Checker is Type:
  Checker{check: @+path: String -> IO(S.Answer)}

# the checker's answer for a path
def check(ck: Checker, +path: String) -> IO(S.Answer):  # noqa: L001 effect accessor
  Checker{c} = ck
  c(path)
