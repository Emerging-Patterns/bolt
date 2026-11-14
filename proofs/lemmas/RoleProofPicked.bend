# proof files picked by role, kept apart from laws, plus the unsafe path
# compares
import Base
import ../../src/paths.bend as Paths
import ../../src/role.bend as Role
import ../../laws/RoleProofNamed.bend as L1

# unsafe (laws/UnsafeReportsReachableForeignDefs.bend), the reach. Paths compare with String.eq, so the
# proofs need it sound and reflexive, down to the words a U32 is made of, as
# src/PROOF.bend's cfg4.seq does.

# Unit for False, Empty for True
def unsafe.false_ty(b: Bool) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      Empty

# False is never True
law unsafe.false_true:
  for e: {False{} == True{} : Bool}
  Empty

def unsafe.false_true(e):
  %e : unsafe.false_ty(_)
  Unit{}

# words that compare equal, bit by bit past the first: the rest equal, the
# first bits the same
law unsafe.weq.arm:
  for -p: Nat
  for -at: Word(p)
  for -bt: Word(p)
  for c: Cmp
  for ec: {Word.cmp(p, at, bt) == c : Cmp}
  for ih: {Cmp.is_eq(Word.cmp(p, at, bt)) == True{} : Bool} -> {at == bt : Word(p)}
  for ab: Bool
  for b: Bool
  for e: {Cmp.is_eq(Word.cmp.fin(ab, b, c)) == True{} : Bool}
  {WCon{ab, at} == WCon{b, bt} : Word.Con<p>}

def unsafe.weq.arm(p, at, bt, c, ec, ih, ab, b, e):
  match c:
    case LT{}:
      Empty.absurd({WCon{ab, at} == WCon{b, bt} : Word.Con<p>}, unsafe.false_true(e))
    case GT{}:
      Empty.absurd({WCon{ab, at} == WCon{b, bt} : Word.Con<p>}, unsafe.false_true(e))
    case EQ{}:
      match ab b:
        case False{} False{}:
          Equal.cong(Word(p), Word.Con<p>, w => WCon{False{}, w}, at, bt,
            ih(Equal.cong(Cmp, Bool, x => Cmp.is_eq(x), Word.cmp(p, at, bt), EQ{}, ec)))
        case True{} True{}:
          Equal.cong(Word(p), Word.Con<p>, w => WCon{True{}, w}, at, bt,
            ih(Equal.cong(Cmp, Bool, x => Cmp.is_eq(x), Word.cmp(p, at, bt), EQ{}, ec)))
        case False{} True{}:
          Empty.absurd({WCon{False{}, at} == WCon{True{}, bt} : Word.Con<p>}, unsafe.false_true(e))
        case True{} False{}:
          Empty.absurd({WCon{True{}, at} == WCon{False{}, bt} : Word.Con<p>}, unsafe.false_true(e))

# words that compare equal are equal
law unsafe.weq:
  for n: Nat
  for a: Word(n)
  for b: Word(n)
  for e: {Cmp.is_eq(Word.cmp(n, a, b)) == True{} : Bool}
  {a == b : Word(n)}

def unsafe.weq(n, a, b, e):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+(+p):
      match a b:
        case WCon{ab, +at} WCon{bb, +bt}:
          unsafe.weq.arm(p, at, bt, Word.cmp(p, at, bt), {==}, x => unsafe.weq(p, at, bt, x), ab, bb, e)

# U32s that compare equal are equal
law unsafe.ueq:
  for a: U32
  for b: U32
  for e: {U32.is_eq(a, b) == True{} : Bool}
  {a == b : U32}

def unsafe.ueq(a, b, e):
  match a b:
    case U32{x} U32{y}:
      Equal.cong(Word(32n), U32, w => U32{w}, x, y, unsafe.weq(32n, x, y, e))

# a compare whose first characters already differ answers as they do, whatever
# the rest (String.eq walks with String.order.go since bend 2.0.37)
law unsafe.go_lt:
  for a: String
  for b: String
  {String.order.go(a, b, LT{}) == LT{} : Cmp}

def unsafe.go_lt(a, b):
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{_h, _t}:
      {==}
    case SCon{_h, _t} SNil{}:
      {==}
    case SCon{Chr{_x}, _t1} SCon{Chr{_y}, _t2}:
      {==}

law unsafe.go_gt:
  for a: String
  for b: String
  {String.order.go(a, b, GT{}) == GT{} : Cmp}

def unsafe.go_gt(a, b):
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{_h, _t}:
      {==}
    case SCon{_h, _t} SNil{}:
      {==}
    case SCon{Chr{_x}, _t1} SCon{Chr{_y}, _t2}:
      {==}

# strings whose first characters compare as c and whose compare comes out
# equal: when c is equal and the rest are equal, they are equal
law unsafe.seq.arm:
  for +x: U32
  for +y: U32
  for +t1: String
  for +t2: String
  for c: Cmp
  for ec: {U32.cmp(x, y) == c : Cmp}
  for ih: {String.eq(t1, t2) == True{} : Bool} -> {t1 == t2 : String}
  for e: {Cmp.is_eq(String.order.go(t1, t2, c)) == True{} : Bool}
  {SCon{Chr{x}, t1} == SCon{Chr{y}, t2} : String}

def unsafe.seq.arm(x, y, t1, t2, c, ec, ih, e):
  match c:
    case LT{}:
      g = Equal.cong(Cmp, Bool, z => Cmp.is_eq(z), LT{}, String.order.go(t1, t2, LT{}),
        Equal.sym(Cmp, String.order.go(t1, t2, LT{}), LT{}, unsafe.go_lt(t1, t2)))
      Empty.absurd({SCon{Chr{x}, t1} == SCon{Chr{y}, t2} : String},
        unsafe.false_true(Equal.trans(Bool, False{}, Cmp.is_eq(String.order.go(t1, t2, LT{})), True{}, g, e)))
    case GT{}:
      g = Equal.cong(Cmp, Bool, z => Cmp.is_eq(z), GT{}, String.order.go(t1, t2, GT{}),
        Equal.sym(Cmp, String.order.go(t1, t2, GT{}), GT{}, unsafe.go_gt(t1, t2)))
      Empty.absurd({SCon{Chr{x}, t1} == SCon{Chr{y}, t2} : String},
        unsafe.false_true(Equal.trans(Bool, False{}, Cmp.is_eq(String.order.go(t1, t2, GT{})), True{}, g, e)))
    case EQ{}:
      et = ih(e)
      ex = unsafe.ueq(x, y, Equal.cong(Cmp, Bool, z => Cmp.is_eq(z), U32.cmp(x, y), EQ{}, ec))
      %ex : {SCon{Chr{x}, t1} == SCon{Chr{_}, t2} : String}
      %et : {SCon{Chr{x}, t1} == SCon{Chr{x}, _} : String}
      {==}

# strings that compare equal are equal
law unsafe.seq:
  for a: String
  for b: String
  for e: {String.eq(a, b) == True{} : Bool}
  {a == b : String}

def unsafe.seq(a, b, e):
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{h, t}:
      Empty.absurd({SNil{} == SCon{h, t} : String}, unsafe.false_true(e))
    case SCon{h, t} SNil{}:
      Empty.absurd({SCon{h, t} == SNil{} : String}, unsafe.false_true(e))
    case SCon{Chr{+x}, +t1} SCon{Chr{+y}, +t2}:
      unsafe.seq.arm(x, y, t1, t2, U32.cmp(x, y), {==}, z => unsafe.seq(t1, t2, z), e)

# a role picked by name is a proof file exactly when the second test held,
# when the second holding rules out the first
law role.pick_proof:
  for a: Bool
  for b: Bool
  for hb: {b == True{} : Bool} -> {a == False{} : Bool}
  {Role.is_proof(Bool.pick(Role.Role, a, Role.Laws{}, Bool.pick(Role.Role, b, Role.Proof{}, Role.Plain{}))) == b : Bool}

def role.pick_proof(a, b, hb):
  match a b:
    case True{} True{}:
      Empty.absurd({Role.is_proof(Role.Laws{}) == True{} : Bool},
        unsafe.false_true(Equal.sym(Bool, True{}, False{}, hb({==}))))
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# a PROOF.bend is not a LAWS.bend
law role.excl:
  for +path: String
  for hb: {Paths.is_proof(path) == True{} : Bool}
  {Paths.is_laws(path) == False{} : Bool}

def role.excl(path, hb):
  eb = Equal.sym(String, Paths.base(path), "PROOF.bend", unsafe.seq(Paths.base(path), "PROOF.bend", hb))
  %eb : {String.eq(_, "LAWS.bend") == False{} : Bool}
  {==}

def L1.role_proof_named(path):
  role.pick_proof(Paths.is_laws(path), Paths.is_proof(path), h => role.excl(path, h))
