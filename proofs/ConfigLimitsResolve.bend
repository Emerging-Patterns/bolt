# proofs of laws/ConfigLimitsResolve.bend
import Base
import ../src/config.bend as Config
import ../src/lazy/lazy.bend as Lazy
import ../laws/ConfigLimitsResolve.bend as Laws
import ./lemmas/PublishComparisons.bend as M1

def Laws.limit_reads_number(word, n, e):
  s = Equal.sym(Maybe<&2, U32>, U32.read(word), Some{n}, e)
  %s : {Maybe.default(&2, U32, _, 0) == n : U32}
  {==}

def Laws.limit_unread_is_zero(word, e):
  s = Equal.sym(Maybe<&2, U32>, U32.read(word), None{}, e)
  %s : {Maybe.default(&2, U32, _, 0) == 0 : U32}
  {==}

def Laws.limits_in_file_order(_kids, _body, _rest):
  {==}

def Laws.limit_first_holds(name, max, rest, base):
  s = Equal.sym(Bool, String.eq(name, name), True{}, M1.pub.seq_refl(name))
  %s : {Lazy.stop(U32, _, max, _u => Config.limit.of(rest, name, base)) == max : U32}
  {==}

def Laws.limit_other_skipped(name, other, max, rest, base, e):
  s = Equal.sym(Bool, String.eq(other, name), False{}, e)
  %s : {Lazy.stop(U32, _, max, _u => Config.limit.of(rest, name, base)) == Config.limit.of(rest, name, base) : U32}
  {==}

def Laws.limit_default(_sets, _name, _base):
  {==}
