# A bolt.bend sets a limit by a def whose body is a number:
# `def reach_max() -> U32: 30`. Each such def is one limit, read in file
# order: its name, and the number as a U32, or 0 when the number is not one
# (so a typo shows as findings, not as silence). A config's limit for a name
# is the first limit of that name, and the rule's own default when none
# names it.
import Base
import ../src/config.bend as Config
import ../src/syntax/tree.bend as Tree
import ../src/syntax/bind.bend as Bind

# LAW: a number that reads as a U32 is that limit
law limit_reads_number:
  for word: String
  for +n: U32
  for e: {U32.read(word) == Some{n} : Maybe<&2, U32>}
  {Config.limit.read(word) == n : U32}

# LAW: a number that does not read as a U32 is the limit 0
law limit_unread_is_zero:
  for word: String
  for e: {U32.read(word) == None{} : Maybe<&2, U32>}
  {Config.limit.read(word) == 0 : U32}

# LAW: a def's limit comes before the limits of the defs after it: the
# limits are in file order
law limits_in_file_order:
  for kids: Tree.Node
  for body: Tree.Node
  for rest: Tree.Node
  {Config.limits.go(Tree.NCons{Tree.Stmt{Tree.SDef{}, kids, body}, rest})
    == List.append(&2, Config.Limit,
      Config.limit.one(Bind.declared(kids), Config.first_num(Tree.leaves(body))),
      Config.limits.go(rest)) : List<&2, Config.Limit>}

# LAW: the first limit of a name is the one that holds, whatever follows it
law limit_first_holds:
  for +name: String
  for max: U32
  for rest: List<&2, Config.Limit>
  for base: U32
  {Config.limit.of(Config.Limit{name, max} <> rest, name, base) == max : U32}

# LAW: a limit of another name is passed over
law limit_other_skipped:
  for +name: String
  for +other: String
  for max: U32
  for rest: List<&2, Config.Limit>
  for base: U32
  for e: {String.eq(other, name) == False{} : Bool}
  {Config.limit.of(Config.Limit{other, max} <> rest, name, base) == Config.limit.of(rest, name, base) : U32}

# LAW: a config's limit is read off its limits alone, and with no limit set
# it is the rule's default
law limit_default:
  for sets: List<&2, Config.LevelSet>
  for name: String
  for base: U32
  {Config.limit(Config.Config{sets, Nil{}}, name, base) == base : U32}
