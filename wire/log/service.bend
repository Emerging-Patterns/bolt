# log: an effect service (CPU event loop only): a line of output.
import Base

type Log is Type:
  Log{say: String -> IO(Unit)}

def say(l: Log, text: String) -> IO(Unit):
  Log{f} = l
  f(text)
