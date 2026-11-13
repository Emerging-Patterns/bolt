# proofs of laws/LspUnitsMatchCharsBelowAstral.bend
import Base
import ../src/lazy/lazy.bend as Lazy
import ../src/lsp/enc.bend as Enc
import ../laws/LspUnitsMatchCharsBelowAstral.bend as Laws
import ./lemmas/BoolEmptiness.bend as M1

# an or_else that is False was False on its left
law nav.or_else_left:
  for a: Bool
  for -f: Unit -> Bool
  for h: {Lazy.or_else(a, f) == False{} : Bool}
  {a == False{} : Bool}

def nav.or_else_left(a, _f, h):
  match a:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, M1.true_false(h))
    case False{}:
      {==}

# an or_else that is False was False on its right
law nav.or_else_right:
  for a: Bool
  for -f: Unit -> Bool
  for h: {Lazy.or_else(a, f) == False{} : Bool}
  {f(Unit{}) == False{} : Bool}

def nav.or_else_right(a, f, h):
  match a:
    case True{}:
      Empty.absurd({f(Unit{}) == False{} : Bool}, M1.true_false(h))
    case False{}:
      h

# on a line with no wide char, UTF-16 units are the code points counted
law nav.units_narrow:
  for cs: List<&2, Char>
  for +h: {Enc.wide_in(cs) == False{} : Bool}
  for nn: Nat
  {Enc.units(cs, nn) == nn : Nat}

def nav.units_narrow(cs, h, nn):
  match cs:
    case Nil{}:
      {==}
    case Con{+c, +t}:
      match nn:
        case 0n:
          {==}
        case 1n+p:
          +hw = Equal.sym(Bool, Enc.wide(c), False{}, nav.or_else_left(Enc.wide(c), _u => Enc.wide_in(t), h))
          %hw : {Enc.units.step(_, Enc.units(t, p)) == 1n+p : Nat}
          Equal.cong(Nat, Nat, x => 1n+x, Enc.units(t, p), p,
            nav.units_narrow(t, nav.or_else_right(Enc.wide(c), _u => Enc.wide_in(t), h), p))

# on a line with no wide char, UTF-16 units read back as themselves
law nav.points_narrow:
  for cs: List<&2, Char>
  for +h: {Enc.wide_in(cs) == False{} : Bool}
  for nn: Nat
  {Enc.points(cs, nn) == nn : Nat}

def nav.points_narrow(cs, h, nn):
  match cs:
    case Nil{}:
      {==}
    case Con{+c, +t}:
      match nn:
        case 0n:
          {==}
        case 1n+p:
          +hw = Equal.sym(Bool, Enc.wide(c), False{}, nav.or_else_left(Enc.wide(c), _u => Enc.wide_in(t), h))
          %hw : {1n+Enc.points(t, Enc.points.skip(_, p)) == 1n+p : Nat}
          Equal.cong(Nat, Nat, x => 1n+x, Enc.points(t, p), p,
            nav.points_narrow(t, nav.or_else_right(Enc.wide(c), _u => Enc.wide_in(t), h), p))

# every line of lines with no wide char has none
law nav.chars_narrow:
  for lines: List<&2, String>
  for h: {Enc.wide_any(lines) == False{} : Bool}
  for ii: Nat
  {Enc.wide_in(String.to_list(Maybe.default(&2, String, List.get(&2, String, lines, ii), ""))) == False{} : Bool}

def nav.chars_narrow(lines, h, ii):
  match lines:
    case Nil{}:
      {==}
    case Con{+l, +t}:
      match ii:
        case 0n:
          nav.or_else_left(Enc.wide_in(String.to_list(l)), _u => Enc.wide_any(t), h)
        case 1n+p:
          nav.chars_narrow(t, nav.or_else_right(Enc.wide_in(String.to_list(l)), _u => Enc.wide_any(t), h), p)

def Laws.enc_narrow(lines, h, line, nn):
  +hc = nav.chars_narrow(lines, h, U32.to_nat(line))
  (nav.units_narrow(Enc.chars(lines, line), hc, nn), nav.points_narrow(Enc.chars(lines, line), hc, nn))

def Laws.wide_from_u10000(_xx):
  {==}

def Laws.narrowed_keeps_utf16_with_a_wide_char(lines, e):
  %Equal.sym(Bool, Enc.wide_any(lines), True{}, e) :
    {Bool.pick(Enc.Enc, _, Enc.Utf16{}, Enc.Utf32{}) == Enc.Utf16{} : Enc.Enc}
  {==}

def Laws.narrowed_reads_utf16_as_utf32_without_one(lines, e):
  %Equal.sym(Bool, Enc.wide_any(lines), False{}, e) :
    {Bool.pick(Enc.Enc, _, Enc.Utf16{}, Enc.Utf32{}) == Enc.Utf32{} : Enc.Enc}
  {==}

def Laws.narrowed_keeps_utf32(_wide):
  {==}
