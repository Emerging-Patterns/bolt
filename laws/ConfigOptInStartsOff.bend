# An opt-in rule is off unless its own setting names it. Five rules are
# opt-in, `thunk`, `transcong`, `reach`, `coverage` and `closed`, and no other rule
# of the code table is.
#
# also rests on: laws/LevelOwn.bend
import Base
import ../src/config.bend as Config
import ../src/codes.bend as Codes

# the opt-in rules, as law vocabulary
def opt_ins() -> List<&2, String>:
  ["thunk", "transcong", "reach", "coverage", "closed"]

# does bolt hold a code table row's rule opt-in exactly when the law lists
# it? past the end holds
def opt_in.agrees(mm: Maybe<&2, Codes.Entry>) -> Bool:
  match mm:
    case None{}:
      True{}
    case Some{Codes.Entry{+slug, _id, _grp}}:
      Bool.not(Bool.xor(Config.opt_in(slug), List.contains(~String, ~String.eq, opt_ins(), slug)))

# LAW: an opt-in rule with no setting of its own is off, whatever its group
# says (with one, level_own gives it that setting)
law opt_in_off:
  for +sets: List<&2, Config.LevelSet>
  for +group: String
  for +rule: String
  for h_opt: {Config.opt_in(rule) == True{} : Bool}
  for h_rule: {Config.set_level(sets, rule) == None{} : Maybe<&2, Config.Level>}
  {Config.level(Config.Config{sets}, group, rule) == Config.Off{} : Config.Level}

# LAW: a rule of the code table is opt-in exactly when it is one of the five
law opt_in_rules:
  for +n: Nat
  {opt_in.agrees(List.get(&2, Codes.Entry, Codes.table(), n)) == True{} : Bool}
