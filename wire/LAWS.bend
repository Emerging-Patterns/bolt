# wire: the laws. The human states them; PROOF.bend must prove them.
import Base
import ./monoid/service.bend as M
import ./monoid/sum.bend as Sum
import ./monoid/xor.bend as Xor

# LAW: sum's unit is a right identity
law sum_unit_right:
  for a: U32
  {M.join(Sum.new(), a, M.unit(Sum.new())) == a : U32}

# LAW: xor's unit is a right identity
law xor_unit_right:
  for a: U32
  {M.join(Xor.new(), a, M.unit(Xor.new())) == a : U32}

# LAW: xor's join is associative
law xor_assoc:
  for a: U32
  for b: U32
  for c: U32
  {M.join(Xor.new(), M.join(Xor.new(), a, b), c)
    == M.join(Xor.new(), a, M.join(Xor.new(), b, c)) : U32}
