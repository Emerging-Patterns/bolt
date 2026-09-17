# clock: an effect service (CPU event loop only): the time in milliseconds.
import Base

type Clock is Type:
  Clock{now: Unit -> IO(Nat)}

def now(c: Clock) -> IO(Nat):
  Clock{f} = c
  f(Unit{})
