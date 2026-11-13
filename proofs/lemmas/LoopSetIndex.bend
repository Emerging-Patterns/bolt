# the looping defs gathered with an index of their names are the ones
# gathered with the names alone
import Base
import ../../src/syntax/bind.bend as Bind
import ../../src/lazy/lazy.bend as Lazy
import ../../src/rules/calls.bend as Calls
import ../../src/rules/suspicious/eager.bend as Eager
import ../../src/rules/pedantic/rewalk.bend as Rewalk
import ./BinderIndexIsContains.bend as M1

# eager and rewalk each gather the defs of a file that loop, one pass down the
# defs: a def loops when it calls itself or a looping def above it. Asking the
# names gathered so far for every call is the calls times the looping defs,
# so each walk carries the binder's index of those names beside them
# (loops.fast) and asks that. The index of some names holds a name exactly
# when the list does (laws/BinderIndexFindsItems.bend), and putting a name in
# the index is the index of the names with it in front, so the two walks
# gather the same names for any defs.

# a name put in the index of some names, or not, is the index of the names
# with it in front, or without
law lp.push:
  for deep: Bool
  for +name: String
  for +acc: List<&2, String>
  {Bool.pick(Bind.Index, deep, Bind.index.put(Bind.index.depth(), Bind.key(name), Bind.index(acc), name),
    Bind.index(acc)) == Bind.index(Bool.pick(List<&2, String>, deep, name <> acc, acc)) : Bind.Index}

def lp.push(deep, _name, _acc):
  match deep:
    case True{}:
      {==}
    case False{}:
      {==}

# Eager
# -----

# asking the index of a set is asking the set
law lp.eager.any:
  for cs: List<&2, String>
  for +set: List<&2, String>
  {Eager.any_in(cs, Bind.index(set)) == Eager.loops.any(cs, set) : Bool}

def lp.eager.any(cs, set):
  match cs:
    case Nil{}:
      {==}
    case Con{+c, +t}:
      %Equal.sym(Bool, Bind.indexed(Bind.index(set), c), List.contains(~String, ~String.eq, set, c),
        M1.ic.indexed(set, c)) :
        {Lazy.or_else(_, _u => Eager.any_in(t, Bind.index(set))) == Eager.loops.any(c <> t, set) : Bool}
      %Equal.sym(Bool, Eager.any_in(t, Bind.index(set)), Eager.loops.any(t, set), lp.eager.any(t, set)) :
        {Lazy.or_else(List.contains(~String, ~String.eq, set, c), _u => _) == Eager.loops.any(c <> t, set) : Bool}
      {==}

# the walk that carries the index of its names gathers what the walk that
# carries the names alone gathers
law lp.eager.loops:
  for ds: List<&2, Calls.Def>
  for +acc: List<&2, String>
  {Eager.loops.fast(ds, acc, Bind.index(acc)) == Eager.loops.go(ds, acc) : List<&2, String>}

def lp.eager.loops(ds, acc):
  match ds:
    case Nil{}:
      {==}
    case Con{Calls.Def{+name, +sig, +body}, +rest}:
      +cs = Eager.called(body)
      +self = List.contains(~String, ~String.eq, cs, name)
      +deep = Bool.or(self, Eager.loops.any(cs, acc))
      +next = Bool.pick(List<&2, String>, deep, name <> acc, acc)
      %Equal.sym(Bool, Eager.any_in(cs, Bind.index(acc)), Eager.loops.any(cs, acc), lp.eager.any(cs, acc)) :
        {Eager.loops.fast(rest, Bool.pick(List<&2, String>, Bool.or(self, _), name <> acc, acc),
          Bool.pick(Bind.Index, Bool.or(self, _),
            Bind.index.put(Bind.index.depth(), Bind.key(name), Bind.index(acc), name), Bind.index(acc)))
          == Eager.loops.go(Calls.Def{name, sig, body} <> rest, acc) : List<&2, String>}
      %Equal.sym(Bind.Index,
        Bool.pick(Bind.Index, deep, Bind.index.put(Bind.index.depth(), Bind.key(name), Bind.index(acc), name),
          Bind.index(acc)),
        Bind.index(next), lp.push(deep, name, acc)) :
        {Eager.loops.fast(rest, next, _) == Eager.loops.go(Calls.Def{name, sig, body} <> rest, acc)
          : List<&2, String>}
      lp.eager.loops(rest, next)

# the looping defs of a file are the ones the walk over the names gathers
law lp.eager.all:
  for ds: List<&2, Calls.Def>
  {Eager.loops(ds) == Eager.loops.go(ds, []) : List<&2, String>}

def lp.eager.all(ds):
  lp.eager.loops(ds, [])

# Rewalk
# ------

# asking the index of a set is asking the set
law lp.rewalk.any:
  for cs: List<&2, String>
  for +set: List<&2, String>
  {Rewalk.any_in(cs, Bind.index(set)) == Rewalk.loops.any(cs, set) : Bool}

def lp.rewalk.any(cs, set):
  match cs:
    case Nil{}:
      {==}
    case Con{+c, +t}:
      %Equal.sym(Bool, Bind.indexed(Bind.index(set), c), List.contains(~String, ~String.eq, set, c),
        M1.ic.indexed(set, c)) :
        {Lazy.or_else(_, _u => Rewalk.any_in(t, Bind.index(set))) == Rewalk.loops.any(c <> t, set) : Bool}
      %Equal.sym(Bool, Rewalk.any_in(t, Bind.index(set)), Rewalk.loops.any(t, set), lp.rewalk.any(t, set)) :
        {Lazy.or_else(List.contains(~String, ~String.eq, set, c), _u => _) == Rewalk.loops.any(c <> t, set) : Bool}
      {==}

# the walk that carries the index of its names gathers what the walk that
# carries the names alone gathers
law lp.rewalk.loops:
  for ds: List<&2, Calls.Def>
  for +acc: List<&2, String>
  {Rewalk.loops.fast(ds, acc, Bind.index(acc)) == Rewalk.loops.go(ds, acc) : List<&2, String>}

def lp.rewalk.loops(ds, acc):
  match ds:
    case Nil{}:
      {==}
    case Con{Calls.Def{+name, +sig, +body}, +rest}:
      +cs = Rewalk.called(body)
      +self = List.contains(~String, ~String.eq, cs, name)
      +deep = Bool.or(self, Rewalk.loops.any(cs, acc))
      +next = Bool.pick(List<&2, String>, deep, name <> acc, acc)
      %Equal.sym(Bool, Rewalk.any_in(cs, Bind.index(acc)), Rewalk.loops.any(cs, acc), lp.rewalk.any(cs, acc)) :
        {Rewalk.loops.fast(rest, Bool.pick(List<&2, String>, Bool.or(self, _), name <> acc, acc),
          Bool.pick(Bind.Index, Bool.or(self, _),
            Bind.index.put(Bind.index.depth(), Bind.key(name), Bind.index(acc), name), Bind.index(acc)))
          == Rewalk.loops.go(Calls.Def{name, sig, body} <> rest, acc) : List<&2, String>}
      %Equal.sym(Bind.Index,
        Bool.pick(Bind.Index, deep, Bind.index.put(Bind.index.depth(), Bind.key(name), Bind.index(acc), name),
          Bind.index(acc)),
        Bind.index(next), lp.push(deep, name, acc)) :
        {Rewalk.loops.fast(rest, next, _) == Rewalk.loops.go(Calls.Def{name, sig, body} <> rest, acc)
          : List<&2, String>}
      lp.rewalk.loops(rest, next)

# the looping defs of a file are the ones the walk over the names gathers
law lp.rewalk.all:
  for ds: List<&2, Calls.Def>
  {Rewalk.loops(ds) == Rewalk.loops.go(ds, []) : List<&2, String>}

def lp.rewalk.all(ds):
  lp.rewalk.loops(ds, [])
