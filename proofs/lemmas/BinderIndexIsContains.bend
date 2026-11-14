# the binder's index of some names is List.contains over them
import Base
import ../../src/syntax/bind.bend as Bind
import ../../src/lazy/lazy.bend as Lazy
import ../../laws/BinderIndexFindsItems.bend as L1
import ./BinderIndex.bend as M1

# The index answers as the binder's scan does (laws/BinderIndexFindsItems.bend),
# the scan stops at the first name its own test finds alike, and that test is
# String.eq. So the index of any names is List.contains over them, which is
# what lets a rule ask the index where it asked the list.

# String.eq walks with String.order.go (bend 2.0.37): once the heads differ,
# the order is theirs, whatever the rest
law ic.go_lt:
  for a: String
  for b: String
  {String.order.go(a, b, LT{}) == LT{} : Cmp}

def ic.go_lt(a, b):
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{_h, _t}:
      {==}
    case SCon{_h, _t} SNil{}:
      {==}
    case SCon{Chr{_x}, _t1} SCon{Chr{_y}, _t2}:
      {==}

# and the same once they compare greater
law ic.go_gt:
  for a: String
  for b: String
  {String.order.go(a, b, GT{}) == GT{} : Cmp}

def ic.go_gt(a, b):
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{_h, _t}:
      {==}
    case SCon{_h, _t} SNil{}:
      {==}
    case SCon{Chr{_x}, _t1} SCon{Chr{_y}, _t2}:
      {==}

# a step of `same` is a step of String.eq, whatever the heads compare to
law ic.step:
  for c: Cmp
  for +t1: String
  for +t2: String
  for ih: {Bind.same(t1, t2) == String.eq(t1, t2) : Bool}
  {Lazy.and_then(Cmp.is_eq(c), _u => Bind.same(t1, t2)) == Cmp.is_eq(String.order.go(t1, t2, c)) : Bool}

def ic.step(c, t1, t2, ih):
  match c:
    case LT{}:
      %Equal.sym(Cmp, String.order.go(t1, t2, LT{}), LT{}, ic.go_lt(t1, t2)) :
        {Lazy.and_then(Cmp.is_eq(LT{}), _u => Bind.same(t1, t2)) == Cmp.is_eq(_) : Bool}
      {==}
    case EQ{}:
      ih
    case GT{}:
      %Equal.sym(Cmp, String.order.go(t1, t2, GT{}), GT{}, ic.go_gt(t1, t2)) :
        {Lazy.and_then(Cmp.is_eq(GT{}), _u => Bind.same(t1, t2)) == Cmp.is_eq(_) : Bool}
      {==}

# the binder's name test is String.eq
law ic.alike:
  for a: String
  for b: String
  {Bind.same(a, b) == String.eq(a, b) : Bool}

def ic.alike(a, b):
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{h2, t2}:
      {==}
    case SCon{h1, t1} SNil{}:
      {==}
    case SCon{Chr{+x}, +t1} SCon{Chr{+y}, +t2}:
      ic.step(U32.cmp(x, y), t1, t2, ic.alike(t1, t2))

# a stop at the first True is List.contains's step (List.any.if, bend 2.0.37)
law ic.or_if:
  for a: Bool
  for -x: Bool
  for -y: Bool
  for ih: {x == y : Bool}
  {Lazy.or_else(a, _u => x) == List.any.if(_u => y, a) : Bool}

def ic.or_if(a, _x, _y, ih):
  match a:
    case True{}:
      {==}
    case False{}:
      ih

# the binder's item search is List.contains
law ic.items:
  for names: List<&2, String>
  for +name: String
  {Bind.has_item(names, name) == List.contains(~String, ~String.eq, names, name) : Bool}

def ic.items(names, name):
  match names:
    case Nil{}:
      {==}
    case Con{+h, +rest}:
      Equal.trans(Bool,
        Lazy.or_else(Bind.same(h, name), _u => Bind.has_item(rest, name)),
        List.any.if(_u => List.contains(~String, ~String.eq, rest, name), Bind.same(h, name)),
        List.any.if(_u => List.contains(~String, ~String.eq, rest, name), String.eq(h, name)),
        ic.or_if(Bind.same(h, name), Bind.has_item(rest, name), List.contains(~String, ~String.eq, rest, name),
          ic.items(rest, name)),
        Equal.cong(Bool, Bool, z => List.any.if(_u => List.contains(~String, ~String.eq, rest, name), z),
          Bind.same(h, name), String.eq(h, name), ic.alike(h, name)))

# the binder's index of the items is List.contains over them
law ic.indexed:
  for +its: List<&2, String>
  for +name: String
  {Bind.indexed(Bind.index(its), name) == List.contains(~String, ~String.eq, its, name) : Bool}

def ic.indexed(its, name):
  Equal.trans(Bool, Bind.indexed(Bind.index(its), name), Bind.has_item(its, name),
    List.contains(~String, ~String.eq, its, name), L1.index_finds(its, name), ic.items(its, name))
