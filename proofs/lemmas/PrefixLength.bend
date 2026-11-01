# the rule's length of a literal is the laws'
import Base
import ../../src/rules/suspicious/prefix.bend as Prefix
import ../../laws/defs/PrefixLength.bend as D1

# the rule's length of a literal's rest is the law's, from every place
law prefix.len:
  for tt: String
  for +mm: Prefix.Mode
  {Prefix.len.go(tt, mm) == D1.prefix_len_go(tt, mm) : Nat}

def prefix.len(tt, mm):
  match tt:
    case SNil{}:
      {==}
    case SCon{+cc, rest}:
      match mm:
        case Prefix.MOpen{}:
          +nx = Prefix.len.next(Prefix.MOpen{}, cc)
          Equal.cong(Nat, Nat, z => Nat.add(Prefix.len.add(Prefix.MOpen{}, cc), z), Prefix.len.go(rest, nx),
            D1.prefix_len_go(rest, nx), prefix.len(rest, nx))
        case Prefix.MPlain{}:
          +nx = Prefix.len.next(Prefix.MPlain{}, cc)
          Equal.cong(Nat, Nat, z => Nat.add(Prefix.len.add(Prefix.MPlain{}, cc), z), Prefix.len.go(rest, nx),
            D1.prefix_len_go(rest, nx), prefix.len(rest, nx))
        case Prefix.MEsc{}:
          +nx = Prefix.len.next(Prefix.MEsc{}, cc)
          Equal.cong(Nat, Nat, z => Nat.add(Prefix.len.add(Prefix.MEsc{}, cc), z), Prefix.len.go(rest, nx),
            D1.prefix_len_go(rest, nx), prefix.len(rest, nx))
        case Prefix.MUni{}:
          +nx = Prefix.len.next(Prefix.MUni{}, cc)
          Equal.cong(Nat, Nat, z => Nat.add(Prefix.len.add(Prefix.MUni{}, cc), z), Prefix.len.go(rest, nx),
            D1.prefix_len_go(rest, nx), prefix.len(rest, nx))
        case Prefix.MDone{}:
          +nx = Prefix.len.next(Prefix.MDone{}, cc)
          Equal.cong(Nat, Nat, z => Nat.add(Prefix.len.add(Prefix.MDone{}, cc), z), Prefix.len.go(rest, nx),
            D1.prefix_len_go(rest, nx), prefix.len(rest, nx))

# the rule's test of a take's length is the law's
law prefix.fits:
  for +kk: String
  for +lit: String
  {Prefix.fits(kk, lit) == D1.prefix_fits(kk, lit) : Bool}

def prefix.fits(kk, lit):
  Equal.cong(Nat, Bool, n => String.eq(kk, Nat.show(n) ++ "n"), Prefix.len.go(lit, Prefix.MOpen{}),
    D1.prefix_len_go(lit, Prefix.MOpen{}), prefix.len(lit, Prefix.MOpen{}))
