# wiring: a consumer of two effect services, run under two containers
import Base
import ../clock/service.bend as Clock
import ../clock/fake.bend as FakeClock
import ../log/service.bend as Log
import ../log/real.bend as RealLog
import ../log/quiet.bend as QuietLog

# the consumer: touches its services only through their accessors
def stamp(~clock: Clock.Clock, ~log: Log.Log, msg: String) -> IO(Unit):
  do IO<Unit>:
    t : Nat <- Clock.now(clock)
    Log.say(log, Nat.show(t) ++ " " ++ msg)

# a container is the defs naming each implementation; swap them to rewire
def test.clock() -> Clock.Clock:
  FakeClock.new()

def test.log() -> Log.Log:
  RealLog.new()

def mute.log() -> Log.Log:
  QuietLog.new()

def main() -> IO(Unit):
  do IO<Unit>:
    stamp(~test.clock(), ~test.log(), "hello")
    stamp(~test.clock(), ~mute.log(), "unheard")
    stamp(~test.clock(), ~test.log(), "again")

#|42 hello
#|42 again
