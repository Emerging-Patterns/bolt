# lemmas the proofs share
import Base
import ../../src/finding.bend as F
import ../../src/lazy/lazy.bend as Lazy

# the length of two lists appended is the sum of theirs
law esc.app:
  for a: List<&2, F.Finding>
  for b: List<&2, F.Finding>
  {List.length(&2, F.Finding, List.append(&2, F.Finding, a, b))
    == Nat.add(List.length(&2, F.Finding, a), List.length(&2, F.Finding, b)) : Nat}

def esc.app(a, b):
  match a:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, F.Finding, List.append(&2, F.Finding, t, b)),
        Nat.add(List.length(&2, F.Finding, t), List.length(&2, F.Finding, b)), esc.app(t, b))

# equal summands give equal sums
law esc.add:
  for -a: Nat
  for -b: Nat
  for -c: Nat
  for -d: Nat
  for e1: {a == b : Nat}
  for e2: {c == d : Nat}
  {Nat.add(a, c) == Nat.add(b, d) : Nat}

def esc.add(a, b, c, d, e1, e2):
  Equal.trans(Nat, Nat.add(a, c), Nat.add(b, c), Nat.add(b, d), Equal.cong(Nat, Nat, x => Nat.add(x, c), a, b, e1),
    Equal.cong(Nat, Nat, y => Nat.add(b, y), c, d, e2))

# an early exit to no findings counts 0, else what the rest counts
law param.stop:
  for b: Bool
  for -more: List<&2, F.Finding>
  for -m: Nat
  for ih: {List.length(&2, F.Finding, more) == m : Nat}
  {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, b, [], _u => more))
    == Bool.pick(Nat, b, 0n, m) : Nat}

def param.stop(b, _more, _m, ih):
  match b:
    case True{}:
      {==}
    case False{}:
      ih

# a lone finding when b holds counts one, else none
law chars.one:
  for b: Bool
  for -x: F.Finding
  {List.length(&2, F.Finding, Bool.pick(List<&2, F.Finding>, b, [x], [])) == Bool.pick(Nat, b, 1n, 0n) : Nat}

def chars.one(b, _x):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# adding nothing leaves a Nat as it was
law tail.zero:
  for n: Nat
  {Nat.add(n, 0n) == n : Nat}

def tail.zero(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(p, 0n), p, tail.zero(p))

# two joined finding lists count the sum of theirs
law tail.cat2:
  for +a: List<&2, F.Finding>
  for +b: List<&2, F.Finding>
  {List.length(&2, F.Finding, List.concat(&2, F.Finding, [a, b]))
    == Nat.add(List.length(&2, F.Finding, a), List.length(&2, F.Finding, b)) : Nat}

def tail.cat2(a, b):
  Equal.trans(Nat,
    List.length(&2, F.Finding, List.append(&2, F.Finding, a, List.append(&2, F.Finding, b, Nil{}))),
    Nat.add(List.length(&2, F.Finding, a), List.length(&2, F.Finding, List.append(&2, F.Finding, b, Nil{}))),
    Nat.add(List.length(&2, F.Finding, a), List.length(&2, F.Finding, b)),
    esc.app(a, List.append(&2, F.Finding, b, Nil{})),
    Equal.cong(Nat, Nat, x => Nat.add(List.length(&2, F.Finding, a), x),
      List.length(&2, F.Finding, List.append(&2, F.Finding, b, Nil{})), List.length(&2, F.Finding, b),
      Equal.trans(Nat, List.length(&2, F.Finding, List.append(&2, F.Finding, b, Nil{})),
        Nat.add(List.length(&2, F.Finding, b), 0n), List.length(&2, F.Finding, b),
        esc.app(b, Nil{}), tail.zero(List.length(&2, F.Finding, b)))))

# three joined finding lists count the sum of theirs
law tail.cat3:
  for +a: List<&2, F.Finding>
  for +b: List<&2, F.Finding>
  for +c: List<&2, F.Finding>
  {List.length(&2, F.Finding, List.concat(&2, F.Finding, [a, b, c]))
    == Nat.add(List.length(&2, F.Finding, a),
      Nat.add(List.length(&2, F.Finding, b), List.length(&2, F.Finding, c))) : Nat}

def tail.cat3(a, b, c):
  Equal.trans(Nat,
    List.length(&2, F.Finding, List.append(&2, F.Finding, a, List.concat(&2, F.Finding, [b, c]))),
    Nat.add(List.length(&2, F.Finding, a), List.length(&2, F.Finding, List.concat(&2, F.Finding, [b, c]))),
    Nat.add(List.length(&2, F.Finding, a),
      Nat.add(List.length(&2, F.Finding, b), List.length(&2, F.Finding, c))),
    esc.app(a, List.concat(&2, F.Finding, [b, c])),
    Equal.cong(Nat, Nat, x => Nat.add(List.length(&2, F.Finding, a), x),
      List.length(&2, F.Finding, List.concat(&2, F.Finding, [b, c])),
      Nat.add(List.length(&2, F.Finding, b), List.length(&2, F.Finding, c)), tail.cat2(b, c)))

# a def's findings count the walk's when its guard keeps it, else none
law tail.stop:
  for b: Bool
  for -more: List<&2, F.Finding>
  for -m: Nat
  for ih: {List.length(&2, F.Finding, more) == m : Nat}
  {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, Bool.not(b), [], _u => more))
    == Bool.pick(Nat, b, m, 0n) : Nat}

def tail.stop(b, _more, _m, ih):
  match b:
    case True{}:
      ih
    case False{}:
      {==}

# The match rules (laws/ArmsReportCoveredNatArms.bend, laws/CharsReportManyCharArms.bend). A rule reads a case
# pattern through nested patterns, so each proof below takes the tree apart one
# constructor at a time, every constructor named, until the rule's match and
# the law's both reduce.

# a list with nothing appended is as long as before
law arms.nil:
  for xs: List<&2, F.Finding>
  {List.length(&2, F.Finding, List.append(&2, F.Finding, xs, Nil{})) == List.length(&2, F.Finding, xs) : Nat}

def arms.nil(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, F.Finding, List.append(&2, F.Finding, t, Nil{})), List.length(&2,
        F.Finding, t), arms.nil(t))

# three lists joined are as long as the three together
law arms.cat:
  for +a: List<&2, F.Finding>
  for +b: List<&2, F.Finding>
  for +c: List<&2, F.Finding>
  {List.length(&2, F.Finding, List.concat(&2, F.Finding, [a, b, c])) == Nat.add(List.length(&2, F.Finding, a),
      Nat.add(List.length(&2, F.Finding, b), List.length(&2, F.Finding, c))) : Nat}

def arms.cat(a, b, c):
  Equal.trans(Nat, List.length(&2, F.Finding, List.append(&2, F.Finding, a, List.append(&2, F.Finding, b,
    List.append(&2, F.Finding, c, Nil{})))), Nat.add(List.length(&2, F.Finding, a), List.length(&2, F.Finding,
    List.append(&2, F.Finding, b, List.append(&2, F.Finding, c, Nil{})))),
    Nat.add(List.length(&2, F.Finding, a), Nat.add(List.length(&2, F.Finding, b), List.length(&2, F.Finding, c))),
    esc.app(a, List.append(&2, F.Finding, b, List.append(&2, F.Finding, c, Nil{}))),
    Equal.cong(Nat, Nat, n => Nat.add(List.length(&2, F.Finding, a), n), List.length(&2, F.Finding, List.append(&2,
      F.Finding, b, List.append(&2, F.Finding, c, Nil{}))), Nat.add(List.length(&2, F.Finding, b), List.length(&2,
      F.Finding, c)),
      Equal.trans(Nat, List.length(&2, F.Finding, List.append(&2, F.Finding, b, List.append(&2, F.Finding, c, Nil{}))),
        Nat.add(List.length(&2, F.Finding, b), List.length(&2, F.Finding, List.append(&2, F.Finding, c, Nil{}))),
        Nat.add(List.length(&2, F.Finding, b), List.length(&2, F.Finding, c)),
        esc.app(b, List.append(&2, F.Finding, c, Nil{})),
        Equal.cong(Nat, Nat, n => Nat.add(List.length(&2, F.Finding, b), n), List.length(&2, F.Finding, List.append(&2,
          F.Finding, c, Nil{})), List.length(&2, F.Finding, c), arms.nil(c)))))

# an early exit on the negation counts as a pick on the condition
law arms.flip:
  for s: Bool
  for -x: Nat
  {Bool.pick(Nat, Bool.not(s), 0n, x) == Bool.pick(Nat, s, x, 0n) : Nat}

def arms.flip(s, _x):
  match s:
    case True{}:
      {==}
    case False{}:
      {==}

# equal summands give equal sums, the second of three
law arms.add3:
  for -a: Nat
  for -b: Nat
  for -c: Nat
  for -d: Nat
  for -e: Nat
  for -f: Nat
  for e1: {a == b : Nat}
  for e2: {c == d : Nat}
  for e3: {e == f : Nat}
  {Nat.add(a, Nat.add(c, e)) == Nat.add(b, Nat.add(d, f)) : Nat}

def arms.add3(a, b, c, d, e, f, e1, e2, e3):
  esc.add(a, b, Nat.add(c, e), Nat.add(d, f), e1, esc.add(c, d, e, f, e2, e3))

# The eager Bool combinators (laws/PickReportsSelfCalls.bend, laws/StrictReportsEagerSelfCalls.bend). A walk joins
# the finding lists of a node's parts; each count adds their counts.

# appending Nil keeps a list's length
law pick.nil:
  for a: List<&2, F.Finding>
  {List.length(&2, F.Finding, List.append(&2, F.Finding, a, Nil{})) == List.length(&2, F.Finding, a) : Nat}

def pick.nil(a):
  match a:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, F.Finding, List.append(&2, F.Finding, t, Nil{})),
        List.length(&2, F.Finding, t), pick.nil(t))

# two lists of known lengths appended: the sum
law pick.join:
  for a: List<&2, F.Finding>
  for r: List<&2, F.Finding>
  for -ma: Nat
  for -mr: Nat
  for ea: {List.length(&2, F.Finding, a) == ma : Nat}
  for er: {List.length(&2, F.Finding, r) == mr : Nat}
  {List.length(&2, F.Finding, List.append(&2, F.Finding, a, r)) == Nat.add(ma, mr) : Nat}

def pick.join(a, r, ma, mr, ea, er):
  Equal.trans(Nat, List.length(&2, F.Finding, List.append(&2, F.Finding, a, r)),
    Nat.add(List.length(&2, F.Finding, a), List.length(&2, F.Finding, r)), Nat.add(ma, mr),
    esc.app(a, r), esc.add(List.length(&2, F.Finding, a), ma, List.length(&2, F.Finding, r), mr, ea, er))

# the last list of a join: Nil appended
law pick.last:
  for b: List<&2, F.Finding>
  for -mb: Nat
  for eb: {List.length(&2, F.Finding, b) == mb : Nat}
  {List.length(&2, F.Finding, List.append(&2, F.Finding, b, Nil{})) == mb : Nat}

def pick.last(b, mb, eb):
  Equal.trans(Nat, List.length(&2, F.Finding, List.append(&2, F.Finding, b, Nil{})),
    List.length(&2, F.Finding, b), mb, pick.nil(b), eb)

# the findings of lists reversed onto ys: the lengths of acc summed onto theirs
def pick.sum(acc: List<&2, List<&2, F.Finding>>, n: Nat) -> Nat:
  match acc:
    case Nil{}:
      n
    case Con{h, t}:
      pick.sum(t, Nat.add(List.length(&2, F.Finding, h), n))

# reversing finding lists onto ys and joining them: acc's lengths onto ys's
law pick.rev:
  for acc: List<&2, List<&2, F.Finding>>
  for +ys: List<&2, List<&2, F.Finding>>
  {List.length(&2, F.Finding, List.concat(&2, F.Finding, List.reverse.go(&2, List<&2, F.Finding>, acc, ys)))
    == pick.sum(acc, List.length(&2, F.Finding, List.concat(&2, F.Finding, ys))) : Nat}

def pick.rev(acc, ys):
  match acc:
    case Nil{}:
      {==}
    case Con{+h, t}:
      Equal.trans(Nat,
        List.length(&2, F.Finding, List.concat(&2, F.Finding, List.reverse.go(&2, List<&2, F.Finding>, t, h <> ys))),
        pick.sum(t, List.length(&2, F.Finding, List.concat(&2, F.Finding, h <> ys))),
        pick.sum(t, Nat.add(List.length(&2, F.Finding, h), List.length(&2, F.Finding, List.concat(&2, F.Finding, ys)))),
        pick.rev(t, h <> ys),
        Equal.cong(Nat, Nat, n => pick.sum(t, n), List.length(&2, F.Finding, List.concat(&2, F.Finding, h <> ys)),
          Nat.add(List.length(&2, F.Finding, h), List.length(&2, F.Finding, List.concat(&2, F.Finding, ys))),
          esc.app(h, List.concat(&2, F.Finding, ys))))

# The table rules, table (laws/TableReportsFixedTableAccess.bend) and ring (laws/RingReportsDropAppendRotation.bend): a
# walk
# joins a site's own findings with its group's and the rest's, so its count
# is their sum; the def walk sums the defs the guard keeps (pick.sum).

# two joined lists that count m and n count m + n
law table.two:
  for +a: List<&2, F.Finding>
  for +b: List<&2, F.Finding>
  for -m: Nat
  for -n: Nat
  for e1: {List.length(&2, F.Finding, a) == m : Nat}
  for e2: {List.length(&2, F.Finding, b) == n : Nat}
  {List.length(&2, F.Finding, List.concat(&2, F.Finding, [a, b])) == Nat.add(m, n) : Nat}

def table.two(a, b, m, n, e1, e2):
  Equal.trans(Nat, List.length(&2, F.Finding, List.concat(&2, F.Finding, [a, b])),
    Nat.add(List.length(&2, F.Finding, a), List.length(&2, F.Finding, b)), Nat.add(m, n),
    tail.cat2(a, b), esc.add(List.length(&2, F.Finding, a), m, List.length(&2, F.Finding, b), n, e1, e2))

# three joined lists that count m, n and p count m + (n + p)
law table.three:
  for +a: List<&2, F.Finding>
  for +b: List<&2, F.Finding>
  for +c: List<&2, F.Finding>
  for -m: Nat
  for -n: Nat
  for -p: Nat
  for e1: {List.length(&2, F.Finding, a) == m : Nat}
  for e2: {List.length(&2, F.Finding, b) == n : Nat}
  for e3: {List.length(&2, F.Finding, c) == p : Nat}
  {List.length(&2, F.Finding, List.concat(&2, F.Finding, [a, b, c])) == Nat.add(m, Nat.add(n, p)) : Nat}

def table.three(a, b, c, m, n, p, e1, e2, e3):
  Equal.trans(Nat, List.length(&2, F.Finding, List.concat(&2, F.Finding, [a, b, c])),
    Nat.add(List.length(&2, F.Finding, a), Nat.add(List.length(&2, F.Finding, b), List.length(&2, F.Finding, c))),
    Nat.add(m, Nat.add(n, p)),
    tail.cat3(a, b, c),
    esc.add(List.length(&2, F.Finding, a), m,
      Nat.add(List.length(&2, F.Finding, b), List.length(&2, F.Finding, c)), Nat.add(n, p), e1,
      esc.add(List.length(&2, F.Finding, b), n, List.length(&2, F.Finding, c), p, e2, e3)))

# adding a one-or-none is picking between the successor and the Nat
law fuel.addpick:
  for l: Bool
  for -m: Nat
  {Nat.add(Bool.pick(Nat, l, 1n, 0n), m) == Bool.pick(Nat, l, 1n+m, m) : Nat}

def fuel.addpick(l, _m):
  match l:
    case True{}:
      {==}
    case False{}:
      {==}

# two joined finding lists count the sum of theirs
law fuel.two:
  for a: List<&2, F.Finding>
  for +b: List<&2, F.Finding>
  for -ma: Nat
  for -mb: Nat
  for ea: {List.length(&2, F.Finding, a) == ma : Nat}
  for eb: {List.length(&2, F.Finding, b) == mb : Nat}
  {List.length(&2, F.Finding, List.concat(&2, F.Finding, [a, b])) == Nat.add(ma, mb) : Nat}

def fuel.two(a, b, ma, mb, ea, eb):
  pick.join(a, List.append(&2, F.Finding, b, Nil{}), ma, mb, ea, pick.last(b, mb, eb))

# three joined finding lists count the sum of theirs
law fuel.three:
  for a: List<&2, F.Finding>
  for +b: List<&2, F.Finding>
  for +c: List<&2, F.Finding>
  for -ma: Nat
  for -mb: Nat
  for -mc: Nat
  for ea: {List.length(&2, F.Finding, a) == ma : Nat}
  for eb: {List.length(&2, F.Finding, b) == mb : Nat}
  for ec: {List.length(&2, F.Finding, c) == mc : Nat}
  {List.length(&2, F.Finding, List.concat(&2, F.Finding, [a, b, c])) == Nat.add(ma, Nat.add(mb, mc)) : Nat}

def fuel.three(a, b, c, ma, mb, mc, ea, eb, ec):
  pick.join(a, List.concat(&2, F.Finding, [b, c]), ma, Nat.add(mb, mc), ea, fuel.two(b, c, mb, mc, eb, ec))

# a finding when b, none otherwise, counts one when b
law thunk.one:
  for b: Bool
  for -x: F.Finding
  {List.length(&2, F.Finding, Bool.pick(List<&2, F.Finding>, b, [x], [])) == Bool.pick(Nat, b, 1n, 0n) : Nat}

def thunk.one(b, _x):
  match b:
    case True{}: {==}
    case False{}: {==}
