# `param` reports exactly one finding for each parameter binder whose name is
# shorter than two characters, unless the name is one capital letter (a type
# parameter) or the parameter is bare or typed `: Quant` (a quantity), none
# for any other binder, and none at all in a PROOF.bend.
import Base
import ../src/finding.bend as F
import ../src/rules/style/param.bend as Param
import ../src/syntax/bind.bend as Bind
import ../src/paths.bend as Paths
import ../src/rules/tokens.bend as T

# one char, and a capital
def one_upper(cs: List<&2, Char>) -> Bool:
  match cs:
    case Con{ch, Nil{}}:
      Char.is_upper(ch)
    case Con{ch, Con{d2, r}}:
      False{}
    case Nil{}:
      False{}

# a parameter binder shorter than 2 chars that is neither one capital (a type
# parameter) nor bare or typed `: Quant` (a quantity), its note read with
# each string literal cut to its quote
def too_short(kk: Bind.BindKind, +nm: String, +note: String) -> Bool:
  match kk:
    case Bind.KParam{}:
      Bool.and(Nat.is_lt(String.length(nm), 2n),
        Bool.not(Bool.or(one_upper(String.to_list(nm)),
          Bool.or(Bool.not(String.contains(T.code(note), ":")), String.ends_with(T.code(note), ": Quant")))))
    case other:
      False{}

# how many binders are parameters too short
def short_count(binds: List<&2, Bind.Bind>) -> Nat:
  match binds:
    case Nil{}:
      0n
    case Con{Bind.Bind{+nm, line, col, kk, +note}, rest}:
      +m = short_count(rest)
      Bool.pick(Nat, too_short(kk, nm, note), 1n+m, m)

# LAW: over the binder list, param reports one finding for each parameter
# binder shorter than 2 chars that is neither one capital nor bare or typed
# `: Quant`, none for any other binder, and none at all in a PROOF.bend
law param_counts:
  for binds: List<&2, Bind.Bind>
  for +path: String
  {List.length(&2, F.Finding, Param.check.on(binds, path))
    == Bool.pick(Nat, Paths.is_proof(path), 0n, short_count(binds)) : Nat}
