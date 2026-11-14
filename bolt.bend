# bolt.bend: how bolt lints this repo. Every rule is an error except `coverage`,
# which warns until the laws exist: the gate must see no errors. The opt-in
# and pedantic rules are turned on by name or group below. See
# src/config.bend for the groups and levels.
import Base

# what will fail or blow up
def correctness() -> String:
  "error"

# what is probably a slip
def suspicious() -> String:
  "error"

# what is slow but right
def perf() -> String:
  "error"

# comments and whitespace
def style() -> String:
  "error"

# advice that is noisy on idiomatic code, held here all the same: foreign,
# strict, fuel, index and rewalk were errors here before they moved
def pedantic() -> String:
  "error"

# but not a tail call on every step
def tail() -> String:
  "off"

# a def named by no law, IO included: advice while guarantees are pending,
# since deleting the closed laws left defs no law names. That rule
# is `coverage` (L001), opt-in, so only its own setting turns it on.
def coverage() -> String:
  "warn"

# a one-character name read far below its binder (opt-in)
def reach() -> String:
  "error"

# a law with no binder (opt-in)
def closed() -> String:
  "error"
