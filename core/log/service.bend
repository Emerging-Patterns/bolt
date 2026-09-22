# log: an effect service (CPU event loop only): a line of output.
import Base

# effect service: a line out
type Log is Type:
  Log{say: String -> IO(Unit)}

# a line, to a log
def say(ll: Log, text: String) -> IO(Unit):
  Log{f} = ll
  f(text)
