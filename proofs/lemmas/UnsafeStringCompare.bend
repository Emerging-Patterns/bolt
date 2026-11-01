# string and word comparison reflexivity for the unsafe reach
import Base

# a word compares equal to itself
law unsafe.wrefl:
  for n: Nat
  for +a: Word(n)
  {Word.cmp(n, a, a) == EQ{} : Cmp}

def unsafe.wrefl(n, a):
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      match a:
        case WCon{False{}, +at}:
          %Equal.sym(Cmp, Word.cmp(p, at, at), EQ{}, unsafe.wrefl(p, at)) :
            {Word.cmp.fin(False{}, False{}, _) == EQ{} : Cmp}
          {==}
        case WCon{True{}, +at}:
          %Equal.sym(Cmp, Word.cmp(p, at, at), EQ{}, unsafe.wrefl(p, at)) :
            {Word.cmp.fin(True{}, True{}, _) == EQ{} : Cmp}
          {==}

# a string is String.eq to itself
law unsafe.srefl:
  for +s: String
  {String.eq(s, s) == True{} : Bool}

def unsafe.srefl(s):
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{U32{+w}}, +t}:
      %Equal.sym(Cmp, Word.cmp(32n, w, w), EQ{}, unsafe.wrefl(32n, w)) :
        {Cmp.is_eq(String.order.go(t, t, _)) == True{} : Bool}
      unsafe.srefl(t)
