# the rule's length of a literal is the laws'
import Base
import ../../src/rules/suspicious/prefix.bend as Prefix
import ../../laws/defs/PrefixLength.bend as D1

# the rule's length of a literal's rest is the law's, from every place
law prefix.len:
  for t: String
  for +m: Prefix.Mode
  {Prefix.len.go(t, m) == D1.prefix_len_go(t, m) : Nat}

def prefix.len(t, m):
  match t:
    case SNil{}:
      {==}
    case SCon{+c, rest}:
      match m:
        case Prefix.MOpen{}:
          +nx = Prefix.len.next(Prefix.MOpen{}, c)
          Equal.cong(Nat, Nat, z => Nat.add(Prefix.len.add(Prefix.MOpen{}, c), z), Prefix.len.go(rest, nx),
            D1.prefix_len_go(rest, nx), prefix.len(rest, nx))
        case Prefix.MPlain{}:
          +nx = Prefix.len.next(Prefix.MPlain{}, c)
          Equal.cong(Nat, Nat, z => Nat.add(Prefix.len.add(Prefix.MPlain{}, c), z), Prefix.len.go(rest, nx),
            D1.prefix_len_go(rest, nx), prefix.len(rest, nx))
        case Prefix.MEsc{}:
          +nx = Prefix.len.next(Prefix.MEsc{}, c)
          Equal.cong(Nat, Nat, z => Nat.add(Prefix.len.add(Prefix.MEsc{}, c), z), Prefix.len.go(rest, nx),
            D1.prefix_len_go(rest, nx), prefix.len(rest, nx))
        case Prefix.MUni{}:
          +nx = Prefix.len.next(Prefix.MUni{}, c)
          Equal.cong(Nat, Nat, z => Nat.add(Prefix.len.add(Prefix.MUni{}, c), z), Prefix.len.go(rest, nx),
            D1.prefix_len_go(rest, nx), prefix.len(rest, nx))
        case Prefix.MDone{}:
          +nx = Prefix.len.next(Prefix.MDone{}, c)
          Equal.cong(Nat, Nat, z => Nat.add(Prefix.len.add(Prefix.MDone{}, c), z), Prefix.len.go(rest, nx),
            D1.prefix_len_go(rest, nx), prefix.len(rest, nx))

# the rule's test of a take's length is the law's
law prefix.fits:
  for +k: String
  for +lit: String
  {Prefix.fits(k, lit) == D1.prefix_fits(k, lit) : Bool}

def prefix.fits(k, lit):
  Equal.cong(Nat, Bool, n => String.eq(k, Nat.show(n) ++ "n"), Prefix.len.go(lit, Prefix.MOpen{}),
    D1.prefix_len_go(lit, Prefix.MOpen{}), prefix.len(lit, Prefix.MOpen{}))
