# core

Dependency injection for Bend: consumers say what they need, a container says
what they get. Bend has no reflection, so nothing is resolved at runtime:
dependencies are `~` template arguments, inlined at compile time. An injected
service costs nothing, can be called any number of times (a closure could be
called once), a missing or ill-typed one is a checker error at the wiring site,
and its contract can be a proven law.

## The convention

A service is a folder: `service.bend` holds the record type and its accessors,
and each implementation is a file beside it that exports `new()`.

```python
# clock/service.bend -- 1. a service: a record of functions, reached through
# accessor defs
type Clock is Type:
  Clock{now: Unit -> IO(Nat)}

def now(c: Clock) -> IO(Nat):
  Clock{f} = c
  f(Unit{})

# clock/fake.bend -- 2. an implementation: new(), built from top-level defs
import ./service.bend as S

def now(u: Unit) -> IO(Nat):
  IO.pure(Nat, 42n)

def new() -> S.Clock:
  S.Clock{now}

# 3. a consumer: a template that touches the service only through accessors
import ../clock/service.bend as Clock
import ../log/service.bend as Log

def stamp(~clock: Clock.Clock, ~log: Log.Log, msg: String) -> IO(Unit):
  do IO<Unit>:
    t : Nat <- Clock.now(clock)
    Log.say(log, Nat.show(t) ++ " " ++ msg)

# 4. a container: the defs naming each implementation; swap them to rewire
import ../clock/real.bend as RealClock

def app.clock() -> Clock.Clock:
  RealClock.new()

stamp(~app.clock(), ~app.log(), "hello")
```

## Pure and effect services

A **pure** service has no IO in its fields, so its consumers may run under a
`!` call, on the GPU: `Par.fold!(~Sum.new(), ~Index.new(), 20n, 0)` folds 2^20
leaves with an injected monoid and an injected leaf, on the device. An
**effect** service returns `IO` and runs on the CPU event loop only.

| folder | kind | service | implementations |
|--------|------|---------|-----------------|
| `monoid/` | pure | `Monoid{unit, join}` over U32 | `sum`, `xor` |
| `leaf/` | pure | `Leaf{at}`: the value at an index | `one`, `index` |
| `clock/` | effect | `Clock{now}` | `real`, `fake` (always 42) |
| `log/` | effect | `Log{say}` | `real`, `quiet` |
| `check/` | effect | `Reporter{pass, fail}` | `print`, `quiet` |

Consumers: `par/fold.bend` (`fold(~m, ~leaf, n, i)`, a parallel fold) and
`check/kit.bend` (`eq_u32`, `eq_str`, the test kit).

`check` is core used on itself: the kit's reporter is an injected service, and
the kit's own equalities are laws. Other projects that still print a check
do it with `../core/check/kit.bend` and `../core/check/print.bend`.

## Laws

`LAWS.bend` states, through the service interface, what an implementation
promises; `PROOF.bend` proves it. Proven: `xor` has a right identity and is
associative (so any split of an xor fold is sound), `sum` has a right identity.

Open work, not yet stated as laws: associativity of `sum` (a carry-chain
induction over `Word.adc`), the left identities, a Reader-monad `dep.bend` for
wiring chosen at runtime, and a Monoid over any element type.
