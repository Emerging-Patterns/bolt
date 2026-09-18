# log: an effect service (CPU event loop only): a line of output.
import Base

# effect service: a line out
type Log is Type:
  Log{say: String -> IO(Unit)}

# a line, to a log
def say(l: Log, text: String) -> IO(Unit):
  Log{f} = l
  f(text)
