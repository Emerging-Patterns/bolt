# wire: the proofs. `bend PROOF.bend` is the gate.
import Base
import ./monoid/service.bend as M
import ./monoid/sum.bend as Sum
import ./monoid/xor.bend as Xor
import ./LAWS.bend as Laws

law Word.xor_zero:
  for n: Nat
  for w: Word(n)
  {Word.xor(n, w, Word.zero(n)) == w : Word(n)}

def Word.xor_zero(n, w):
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{False{}, t}:
          Equal.cong(Word(p), Word(1n+p), y => WCon{False{}, y},
            Word.xor(p, t, Word.zero(p)), t, Word.xor_zero(p, t))
        case WCon{True{}, t}:
          Equal.cong(Word(p), Word(1n+p), y => WCon{True{}, y},
            Word.xor(p, t, Word.zero(p)), t, Word.xor_zero(p, t))

def Laws.xor_unit_right(a):
  match a:
    case U32{x}:
      Equal.cong(Word(32n), U32, w => U32{w}, Word.xor(32n, x, Word.zero(32n)),
        x, Word.xor_zero(32n, x))

law Word.xor_assoc.arm:
  for -p : Nat
  for -h : Bool
  for -at: Word(p)
  for -bt: Word(p)
  for -ct: Word(p)
  for ih : {Word.xor(p, Word.xor(p, at, bt), ct)
    == Word.xor(p, at, Word.xor(p, bt, ct)) : Word(p)}
  {WCon{h, Word.xor(p, Word.xor(p, at, bt), ct)}
    == WCon{h, Word.xor(p, at, Word.xor(p, bt, ct))} : Word.Con<p>}

law Word.xor_assoc.go:
  for n: Nat
  for a: Word(n)
  for b: Word(n)
  for c: Word(n)
  {Word.xor(n, Word.xor(n, a, b), c) == Word.xor(n, a, Word.xor(n, b, c))
    : Word(n)}

def Word.xor_assoc.arm(p, h, at, bt, ct, ih):
  Equal.cong(Word(p), Word(1n+p), w => WCon{h, w},
    Word.xor(p, Word.xor(p, at, bt), ct), Word.xor(p, at, Word.xor(p, bt, ct)),
    ih)

def Word.xor_assoc.go(n, a, b, c):
  match n:
    case 0n:
      match a b c:
        case WNil{} WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b c:
        case WCon{False{}, at} WCon{False{}, bt} WCon{False{}, ct}:
          Word.xor_assoc.arm(p, False{}, at, bt, ct, Word.xor_assoc.go(p, at, bt, ct))
        case WCon{False{}, at} WCon{False{}, bt} WCon{True{}, ct}:
          Word.xor_assoc.arm(p, True{}, at, bt, ct, Word.xor_assoc.go(p, at, bt, ct))
        case WCon{False{}, at} WCon{True{}, bt} WCon{False{}, ct}:
          Word.xor_assoc.arm(p, True{}, at, bt, ct, Word.xor_assoc.go(p, at, bt, ct))
        case WCon{False{}, at} WCon{True{}, bt} WCon{True{}, ct}:
          Word.xor_assoc.arm(p, False{}, at, bt, ct, Word.xor_assoc.go(p, at, bt, ct))
        case WCon{True{}, at} WCon{False{}, bt} WCon{False{}, ct}:
          Word.xor_assoc.arm(p, True{}, at, bt, ct, Word.xor_assoc.go(p, at, bt, ct))
        case WCon{True{}, at} WCon{False{}, bt} WCon{True{}, ct}:
          Word.xor_assoc.arm(p, False{}, at, bt, ct, Word.xor_assoc.go(p, at, bt, ct))
        case WCon{True{}, at} WCon{True{}, bt} WCon{False{}, ct}:
          Word.xor_assoc.arm(p, False{}, at, bt, ct, Word.xor_assoc.go(p, at, bt, ct))
        case WCon{True{}, at} WCon{True{}, bt} WCon{True{}, ct}:
          Word.xor_assoc.arm(p, True{}, at, bt, ct, Word.xor_assoc.go(p, at, bt, ct))

def Laws.xor_assoc(a, b, c):
  match a b c:
    case U32{x} U32{y} U32{z}:
      Equal.cong(Word(32n), U32, w => U32{w},
        Word.xor(32n, Word.xor(32n, x, y), z),
        Word.xor(32n, x, Word.xor(32n, y, z)), Word.xor_assoc.go(32n, x, y, z))

law Word.add_zero:
  for n: Nat
  for w: Word(n)
  {Word.add(n, w, Word.zero(n)) == w : Word(n)}

def Word.add_zero(n, w):
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{False{}, t}:
          Equal.cong(Word(p), Word(1n+p), y => WCon{False{}, y},
            Word.add(p, t, Word.zero(p)), t, Word.add_zero(p, t))
        case WCon{True{}, t}:
          Equal.cong(Word(p), Word(1n+p), y => WCon{True{}, y},
            Word.add(p, t, Word.zero(p)), t, Word.add_zero(p, t))

def Laws.sum_unit_right(a):
  match a:
    case U32{x}:
      Equal.cong(Word(32n), U32, w => U32{w}, Word.add(32n, x, Word.zero(32n)),
        x, Word.add_zero(32n, x))

def Laws.one_at(_i):
  {==}

def Laws.index_at(_i):
  {==}

def Laws.one_leaf(_i):
  {==}

def Laws.index_leaf(_i):
  {==}

def Laws.fold_leaf(_i):
  {==}

def Laws.fold_split(_p, _i):
  {==}
