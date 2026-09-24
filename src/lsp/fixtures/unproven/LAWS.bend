import Base

# LAW: zero is a right identity of addition
law add_zero:
  for x: Nat
  {Nat.add(x, 0n) == x : Nat}
