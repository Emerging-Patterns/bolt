# addition and join-length facts for the concat rule's counts
import Base
import ../../src/finding.bend as F
import ../../src/lazy/lazy.bend as Lazy
import ../../src/rules/correctness/pick.bend as Pick
import ./Pick.bend as M1

# concat (laws/ConcatReportsAppendingRecursion.bend). The walk joins each self-call's hits, its group's
# and what follows, so the count adds them; the hits and the def walk build
# their lists on an accumulator reversed at the end, so the count carries the
# accumulator's length (or the sum of its lists' lengths) along. Both halves,
# the self-call's and the continuation's
# (laws/ConcatReportsContinuationAppend.bend), share these.

# a plus (1 plus b) is 1 plus (a plus b)
law concat.succ:
  for a: Nat
  for -b: Nat
  {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}

def concat.succ(a, b):
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, n => 1n+n, Nat.add(p, 1n+b), 1n+Nat.add(p, b), concat.succ(p, b))

# a plus 0 is a
law concat.zero:
  for a: Nat
  {Nat.add(a, 0n) == a : Nat}

def concat.zero(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, n => 1n+n, Nat.add(p, 0n), p, concat.zero(p))

# addition regroups
law concat.assoc:
  for a: Nat
  for -b: Nat
  for -c: Nat
  {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}

def concat.assoc(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, n => 1n+n, Nat.add(Nat.add(p, b), c), Nat.add(p, Nat.add(b, c)), concat.assoc(p, b, c))

# the first two of three summands swap
law concat.swap:
  for a: Nat
  for +b: Nat
  for -c: Nat
  {Nat.add(a, Nat.add(b, c)) == Nat.add(b, Nat.add(a, c)) : Nat}

def concat.swap(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.trans(Nat, 1n+Nat.add(p, Nat.add(b, c)), 1n+Nat.add(b, Nat.add(p, c)), Nat.add(b, 1n+Nat.add(p, c)),
        Equal.cong(Nat, Nat, n => 1n+n, Nat.add(p, Nat.add(b, c)), Nat.add(b, Nat.add(p, c)), concat.swap(p, b, c)),
        Equal.sym(Nat, Nat.add(b, 1n+Nat.add(p, c)), 1n+Nat.add(b, Nat.add(p, c)), concat.succ(b, Nat.add(p, c))))

# the lengths of a list of finding lists, summed
def concat.sum(xss: List<&2, List<&2, F.Finding>>) -> Nat:
  match xss:
    case Nil{}:
      0n
    case Con{+h, +t}:
      Nat.add(List.length(&2, F.Finding, h), concat.sum(t))

# a join is as long as its lists together
law concat.flat:
  for xss: List<&2, List<&2, F.Finding>>
  {List.length(&2, F.Finding, List.concat(&2, F.Finding, xss)) == concat.sum(xss) : Nat}

def concat.flat(xss):
  match xss:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Equal.trans(Nat, List.length(&2, F.Finding, List.append(&2, F.Finding, h, List.concat(&2, F.Finding, t))),
        Nat.add(List.length(&2, F.Finding, h), List.length(&2, F.Finding, List.concat(&2, F.Finding, t))),
        Nat.add(List.length(&2, F.Finding, h), concat.sum(t)),
        M1.esc.app(h, List.concat(&2, F.Finding, t)),
        Equal.cong(Nat, Nat, n => Nat.add(List.length(&2, F.Finding, h), n),
          List.length(&2, F.Finding, List.concat(&2, F.Finding, t)), concat.sum(t), concat.flat(t)))

# lists reversed onto others sum to both sums
law concat.rsum:
  for xss: List<&2, List<&2, F.Finding>>
  for yss: List<&2, List<&2, F.Finding>>
  {concat.sum(List.reverse.go(&2, List<&2, F.Finding>, xss, yss)) == Nat.add(concat.sum(xss), concat.sum(yss)) : Nat}

def concat.rsum(xss, yss):
  match xss:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Equal.trans(Nat, concat.sum(List.reverse.go(&2, List<&2, F.Finding>, t, h <> yss)),
        Nat.add(concat.sum(t), Nat.add(List.length(&2, F.Finding, h), concat.sum(yss))),
        Nat.add(Nat.add(List.length(&2, F.Finding, h), concat.sum(t)), concat.sum(yss)),
        concat.rsum(t, h <> yss),
        Equal.trans(Nat, Nat.add(concat.sum(t), Nat.add(List.length(&2, F.Finding, h), concat.sum(yss))),
          Nat.add(List.length(&2, F.Finding, h), Nat.add(concat.sum(t), concat.sum(yss))),
          Nat.add(Nat.add(List.length(&2, F.Finding, h), concat.sum(t)), concat.sum(yss)),
          concat.swap(concat.sum(t), List.length(&2, F.Finding, h), concat.sum(yss)),
          Equal.sym(Nat, Nat.add(Nat.add(List.length(&2, F.Finding, h), concat.sum(t)), concat.sum(yss)),
            Nat.add(List.length(&2, F.Finding, h), Nat.add(concat.sum(t), concat.sum(yss))),
            concat.assoc(List.length(&2, F.Finding, h), concat.sum(t), concat.sum(yss)))))

# two lists joined count what each counts
law concat.two:
  for a: List<&2, F.Finding>
  for +b: List<&2, F.Finding>
  for -x: Nat
  for -y: Nat
  for ea: {List.length(&2, F.Finding, a) == x : Nat}
  for eb: {List.length(&2, F.Finding, b) == y : Nat}
  {List.length(&2, F.Finding, List.concat(&2, F.Finding, [a, b])) == Nat.add(x, y) : Nat}

def concat.two(a, b, x, y, ea, eb):
  Equal.trans(Nat, List.length(&2, F.Finding, List.concat(&2, F.Finding, [a, b])),
    Nat.add(List.length(&2, F.Finding, a), Nat.add(List.length(&2, F.Finding, b), 0n)), Nat.add(x, y),
    concat.flat([a, b]),
    M1.esc.add(List.length(&2, F.Finding, a), x, Nat.add(List.length(&2, F.Finding, b), 0n), y, ea,
      Equal.trans(Nat, Nat.add(List.length(&2, F.Finding, b), 0n), List.length(&2, F.Finding, b), y,
        concat.zero(List.length(&2, F.Finding, b)), eb)))

# three lists joined count what each counts
law concat.three:
  for a: List<&2, F.Finding>
  for b: List<&2, F.Finding>
  for +c: List<&2, F.Finding>
  for -x: Nat
  for -y: Nat
  for -z: Nat
  for ea: {List.length(&2, F.Finding, a) == x : Nat}
  for eb: {List.length(&2, F.Finding, b) == y : Nat}
  for ec: {List.length(&2, F.Finding, c) == z : Nat}
  {List.length(&2, F.Finding, List.concat(&2, F.Finding, [a, b, c])) == Nat.add(x, Nat.add(y, z)) : Nat}

def concat.three(a, b, c, x, y, z, ea, eb, ec):
  Equal.trans(Nat, List.length(&2, F.Finding, List.concat(&2, F.Finding, [a, b, c])),
    Nat.add(List.length(&2, F.Finding, a),
      Nat.add(List.length(&2, F.Finding, b), Nat.add(List.length(&2, F.Finding, c), 0n))),
    Nat.add(x, Nat.add(y, z)),
    concat.flat([a, b, c]),
    M1.esc.add(List.length(&2, F.Finding, a), x,
      Nat.add(List.length(&2, F.Finding, b), Nat.add(List.length(&2, F.Finding, c), 0n)), Nat.add(y, z), ea,
      M1.esc.add(List.length(&2, F.Finding, b), y, Nat.add(List.length(&2, F.Finding, c), 0n), z, eb,
        Equal.trans(Nat, Nat.add(List.length(&2, F.Finding, c), 0n), List.length(&2, F.Finding, c), z,
          concat.zero(List.length(&2, F.Finding, c)), ec))))

# a def's count moves from the front of the sum past the accumulator's
law concat.move:
  for +x: Nat
  for -y: Nat
  for +s: Nat
  for +f: Nat
  for e: {x == y : Nat}
  {Nat.add(Nat.add(x, s), f) == Nat.add(s, Nat.add(y, f)) : Nat}

def concat.move(x, y, s, f, e):
  Equal.trans(Nat, Nat.add(Nat.add(x, s), f), Nat.add(s, Nat.add(x, f)), Nat.add(s, Nat.add(y, f)),
    Equal.trans(Nat, Nat.add(Nat.add(x, s), f), Nat.add(x, Nat.add(s, f)), Nat.add(s, Nat.add(x, f)),
      concat.assoc(x, s, f), concat.swap(x, s, f)),
    Equal.cong(Nat, Nat, n => Nat.add(s, Nat.add(n, f)), x, y, e))

# a list reversed onto another is as long as both
law concat.rev:
  for xs: List<&2, F.Finding>
  for ys: List<&2, F.Finding>
  {List.length(&2, F.Finding, List.reverse.go(&2, F.Finding, xs, ys))
    == Nat.add(List.length(&2, F.Finding, xs), List.length(&2, F.Finding, ys)) : Nat}

def concat.rev(xs, ys):
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Equal.trans(Nat, List.length(&2, F.Finding, List.reverse.go(&2, F.Finding, t, h <> ys)),
        Nat.add(List.length(&2, F.Finding, t), 1n+List.length(&2, F.Finding, ys)),
        1n+Nat.add(List.length(&2, F.Finding, t), List.length(&2, F.Finding, ys)),
        concat.rev(t, h <> ys), concat.succ(List.length(&2, F.Finding, t), List.length(&2, F.Finding, ys)))

# a stop on `not b` runs its thunk exactly when b holds
law concat.stop:
  for b: Bool
  for -more: List<&2, F.Finding>
  for -m: Nat
  for ih: {List.length(&2, F.Finding, more) == m : Nat}
  {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, Bool.not(b), [], _u => more))
    == Bool.pick(Nat, b, m, 0n) : Nat}

def concat.stop(b, _more, _m, ih):
  match b:
    case True{}:
      ih
    case False{}:
      {==}

# a finding in front when the flag holds, counted on either side of a sum
law concat.bump:
  for b: Bool
  for +l: Nat
  for +m: Nat
  {Nat.add(Bool.pick(Nat, b, 1n+l, l), m) == Nat.add(l, Bool.pick(Nat, b, 1n+m, m)) : Nat}

def concat.bump(b, l, m):
  match b:
    case True{}:
      Equal.sym(Nat, Nat.add(l, 1n+m), 1n+Nat.add(l, m), concat.succ(l, m))
    case False{}:
      {==}
