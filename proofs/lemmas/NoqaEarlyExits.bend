# early-exit and/or equal the strict ones in noqa parsing
import Base
import ../../src/lazy/lazy.bend as Lazy

# an early exit is the strict or, once its thunk's value is the other side
law nqp.or_else:
  for a: Bool
  for -x: Bool
  for -y: Bool
  for e: {x == y : Bool}
  {Lazy.or_else(a, _u => x) == Bool.or(a, y) : Bool}

def nqp.or_else(a, _x, _y, e):
  match a:
    case True{}:
      {==}
    case False{}:
      e

# an early exit is the strict and, once its thunk's value is the other side
law nqp.and_then:
  for a: Bool
  for -x: Bool
  for -y: Bool
  for e: {x == y : Bool}
  {Lazy.and_then(a, _u => x) == Bool.and(a, y) : Bool}

def nqp.and_then(a, _x, _y, e):
  match a:
    case True{}:
      e
    case False{}:
      {==}

# an early-exit or over a condition equal to the strict one's
law nqp.or2:
  for -a: Bool
  for b: Bool
  for -x: Bool
  for -y: Bool
  for ea: {a == b : Bool}
  for ex: {x == y : Bool}
  {Lazy.or_else(a, _u => x) == Bool.or(b, y) : Bool}

def nqp.or2(a, b, x, y, ea, ex):
  e = Equal.sym(Bool, a, b, ea)
  %e : {Lazy.or_else(_, _u => x) == Bool.or(b, y) : Bool}
  nqp.or_else(b, x, y, ex)
