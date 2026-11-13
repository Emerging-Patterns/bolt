# proofs of laws/NoqaReportsStaleComments.bend
import Base
import ../src/lazy/lazy.bend as Lazy
import ../src/finding.bend as F
import ../src/noqa.bend as Noqa
import ../src/rules/style/noqa.bend as NoqaRule
import ../src/codes.bend as Codes
import ../laws/NoqaReportsStaleComments.bend as Laws
import ./lemmas/NoqaEarlyExits.bend as M1

# an early-exit and over a condition equal to the strict one's
law nqp.and2:
  for -a: Bool
  for b: Bool
  for -x: Bool
  for -y: Bool
  for ea: {a == b : Bool}
  for ex: {x == y : Bool}
  {Lazy.and_then(a, _u => x) == Bool.and(b, y) : Bool}

def nqp.and2(a, b, x, y, ea, ex):
  e = Equal.sym(Bool, a, b, ea)
  %e : {Lazy.and_then(_, _u => x) == Bool.and(b, y) : Bool}
  M1.nqp.and_then(b, x, y, ex)

# the length of two lists joined is the sum of theirs
law nqp.len_app:
  for xs: List<&2, F.Finding>
  for +ys: List<&2, F.Finding>
  {List.length(&2, F.Finding, List.append(&2, F.Finding, xs, ys))
    == Nat.add(List.length(&2, F.Finding, xs), List.length(&2, F.Finding, ys)) : Nat}

def nqp.len_app(xs, ys):
  match xs:
    case Nil{}:
      {==}
    case Con{_h, +t}:
      Equal.cong(Nat, Nat, m => 1n+m, List.length(&2, F.Finding, List.append(&2, F.Finding, t, ys)),
        Nat.add(List.length(&2, F.Finding, t), List.length(&2, F.Finding, ys)), nqp.len_app(t, ys))

# a finding put onto the rest, or not, counts one or none
law nqp.len_pick:
  for bb: Bool
  for -ff: F.Finding
  for -more: List<&2, F.Finding>
  for -m: Nat
  for ih: {List.length(&2, F.Finding, more) == m : Nat}
  {List.length(&2, F.Finding, Bool.pick(List<&2, F.Finding>, bb, ff <> more, more))
    == Bool.pick(Nat, bb, 1n+m, m) : Nat}

def nqp.len_pick(bb, _ff, more, m, ih):
  match bb:
    case True{}:
      Equal.cong(Nat, Nat, k => 1n+k, List.length(&2, F.Finding, more), m, ih)
    case False{}:
      ih

# the rule's search of the graded findings is the spec's
law nqp.used:
  for gs: List<&2, F.Graded>
  for +path: String
  for +line: U32
  for +code: String
  {NoqaRule.used(gs, path, line, code) == Laws.nq.used(gs, path, line, code) : Bool}

def nqp.used(gs, path, line, code):
  match gs:
    case Nil{}:
      {==}
    case Con{F.Graded{_ll, F.Finding{+p, +l, _col, _len, +rule, _msg}}, +rest}:
      M1.nqp.or2(
        Lazy.and_then(String.eq(p, path),
          _u => Lazy.and_then(U32.is_eq(l, line), _v => String.eq(Codes.code(rule), code))),
        Bool.and(String.eq(p, path), Bool.and(U32.is_eq(l, line), String.eq(Codes.code(rule), code))),
        NoqaRule.used(rest, path, line, code), Laws.nq.used(rest, path, line, code),
        M1.nqp.and_then(String.eq(p, path), Lazy.and_then(U32.is_eq(l, line), _v => String.eq(Codes.code(rule), code)),
          Bool.and(U32.is_eq(l, line), String.eq(Codes.code(rule), code)),
          M1.nqp.and_then(U32.is_eq(l, line), String.eq(Codes.code(rule), code), String.eq(Codes.code(rule), code),
            {==})),
        nqp.used(rest, path, line, code))

# the rule's project code is the spec's: `coverage`
law nqp.project:
  for +code: String
  {NoqaRule.project(code) == Laws.nq.project(code) : Bool}

def nqp.project(_code):
  {==}

# the rule's test of a code is the spec's: judged, and silencing nothing
law nqp.bad:
  for +whole: Bool
  for +c: String
  for +path: String
  for +line: U32
  for +gs: List<&2, F.Graded>
  {Lazy.and_then(NoqaRule.judged(whole, c), _u => Bool.not(NoqaRule.used(gs, path, line, c)))
    == Bool.and(Bool.or(whole, Bool.not(Laws.nq.project(c))), Bool.not(Laws.nq.used(gs, path, line, c))) : Bool}

def nqp.bad(whole, c, path, line, gs):
  nqp.and2(NoqaRule.judged(whole, c), Bool.or(whole, Bool.not(Laws.nq.project(c))),
    Bool.not(NoqaRule.used(gs, path, line, c)), Bool.not(Laws.nq.used(gs, path, line, c)),
    M1.nqp.or_else(whole, Bool.not(NoqaRule.project(c)), Bool.not(Laws.nq.project(c)),
      Equal.cong(Bool, Bool, bb => Bool.not(bb), NoqaRule.project(c), Laws.nq.project(c), nqp.project(c))),
    Equal.cong(Bool, Bool, bb => Bool.not(bb), NoqaRule.used(gs, path, line, c), Laws.nq.used(gs, path, line, c),
      nqp.used(gs, path, line, c)))

# a mark's codes: one finding per code the spec counts
law nqp.codes:
  for cs: List<&2, String>
  for +whole: Bool
  for +path: String
  for +line: U32
  for +col: U32
  for +len: U32
  for +gs: List<&2, F.Graded>
  {List.length(&2, F.Finding, NoqaRule.check.codes(cs, whole, path, line, col, len, gs))
    == Laws.nq.unused(cs, whole, path, line, gs) : Nat}

def nqp.codes(cs, whole, path, line, col, len, gs):
  match cs:
    case Nil{}:
      {==}
    case Con{+c, +rest}:
      e = Equal.sym(Bool,
        Lazy.and_then(NoqaRule.judged(whole, c), _u => Bool.not(NoqaRule.used(gs, path, line, c))),
        Bool.and(Bool.or(whole, Bool.not(Laws.nq.project(c))), Bool.not(Laws.nq.used(gs, path, line, c))),
        nqp.bad(whole, c, path, line, gs))
      %e : {List.length(&2, F.Finding, Bool.pick(List<&2, F.Finding>, _,
          F.Finding{path, line, col, len, "noqa", NoqaRule.say(c)}
            <> NoqaRule.check.codes(rest, whole, path, line, col, len, gs),
          NoqaRule.check.codes(rest, whole, path, line, col, len, gs)))
        == Laws.nq.unused(c <> rest, whole, path, line, gs) : Nat}
      nqp.len_pick(Bool.and(Bool.or(whole, Bool.not(Laws.nq.project(c))), Bool.not(Laws.nq.used(gs, path, line, c))),
        F.Finding{path, line, col, len, "noqa", NoqaRule.say(c)},
        NoqaRule.check.codes(rest, whole, path, line, col, len, gs), Laws.nq.unused(rest, whole, path, line, gs),
        nqp.codes(rest, whole, path, line, col, len, gs))

# a mark: one finding when bare, else the spec's count of its codes
law nqp.mark:
  for mk: Noqa.Mark
  for +whole: Bool
  for +path: String
  for +gs: List<&2, F.Graded>
  {List.length(&2, F.Finding, NoqaRule.check.mark(mk, whole, path, gs)) == Laws.nq.earns(mk, whole, path, gs) : Nat}

def nqp.mark(mk, whole, path, gs):
  match mk:
    case Noqa.Mark{_line, _col, _len, Nil{}}:
      {==}
    case Noqa.Mark{+line, +col, +len, Con{+c, +rest}}:
      nqp.codes(c <> rest, whole, path, line, col, len, gs)

def Laws.noqa_counts(mks, whole, path, gs):
  match mks:
    case Nil{}:
      {==}
    case Con{+mk, +rest}:
      e1 = nqp.mark(mk, whole, path, gs)
      %e1 : {List.length(&2, F.Finding, List.append(&2, F.Finding, NoqaRule.check.mark(mk, whole, path, gs),
          NoqaRule.check(rest, whole, path, gs)))
        == Nat.add(_, Laws.nq.count(rest, whole, path, gs)) : Nat}
      e2 = Laws.noqa_counts(rest, whole, path, gs)
      %e2 : {List.length(&2, F.Finding, List.append(&2, F.Finding, NoqaRule.check.mark(mk, whole, path, gs),
          NoqaRule.check(rest, whole, path, gs)))
        == Nat.add(List.length(&2, F.Finding, NoqaRule.check.mark(mk, whole, path, gs)), _) : Nat}
      nqp.len_app(NoqaRule.check.mark(mk, whole, path, gs), NoqaRule.check(rest, whole, path, gs))

# a stop at the first True is the plain or
law nqr.or_else:
  for c: Bool
  for -x: Bool
  {Lazy.or_else(c, _u => x) == Bool.or(c, x) : Bool}

def nqr.or_else(c, _x):
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

# a test or nothing is the test
law nqr.or_false:
  for c: Bool
  {Bool.or(c, False{}) == c : Bool}

def nqr.or_false(c):
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.known_in_some_row(_s, id, _grp, rest, code):
  nqr.or_else(String.eq(id, code), NoqaRule.known.in(rest, code))

def Laws.known_in_one_row(s, id, grp, code):
  Equal.trans(Bool, NoqaRule.known.in(Codes.Entry{s, id, grp} <> Nil{}, code), Bool.or(String.eq(id, code), False{}),
    String.eq(id, code), Laws.known_in_some_row(s, id, grp, Nil{}, code), nqr.or_false(String.eq(id, code)))
