# core: the laws. The human states them; PROOF.bend must prove them.
import Base
import ./monoid/service.bend as M
import ./monoid/sum.bend as Sum
import ./monoid/xor.bend as Xor
import ./leaf/service.bend as Leaf
import ./leaf/one.bend as One
import ./leaf/index.bend as Index
import ./par/fold.bend as Fold

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

# LAW: the one leaf is 1 at every index
law one_at:
  for i: U32
  {One.at(i) == 1 : U32}

# LAW: the index leaf is its index
law index_at:
  for i: U32
  {Index.at(i) == i : U32}

# LAW: the one leaf, as a service, is One.at
law one_leaf:
  for i: U32
  {Leaf.at(One.new(), i) == One.at(i) : U32}

# LAW: the index leaf, as a service, is Index.at
law index_leaf:
  for i: U32
  {Leaf.at(Index.new(), i) == Index.at(i) : U32}

# LAW: a fold over no levels is the leaf at i
law fold_leaf:
  for i: U32
  {Fold.fold(~Sum.new(), ~One.new(), 0n, i) == Leaf.at(One.new(), i) : U32}

# LAW: a fold over one level more joins the folds of its two halves
law fold_split:
  for p: Nat
  for i: U32
  {Fold.fold(~Sum.new(), ~One.new(), 1n+p, i)
    == M.join(Sum.new(), Fold.fold(~Sum.new(), ~One.new(), p, (i * 2 : U32)),
      Fold.fold(~Sum.new(), ~One.new(), p, (i * 2 + 1 : U32))) : U32}
