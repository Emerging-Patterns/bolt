# clock: an effect service (CPU event loop only): the time in milliseconds.
import Base

# effect service: the time now
type Clock is Type:
  Clock{now: Unit -> IO(Nat)}

# the time, from a clock
def now(c: Clock) -> IO(Nat):
  Clock{f} = c
  f(Unit{})
