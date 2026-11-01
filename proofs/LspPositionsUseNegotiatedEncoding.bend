# proofs of laws/LspPositionsUseNegotiatedEncoding.bend
import Base
import 0xa81e161008ecc2f297c0a3065cb9b188/main.bend as Ezjson
import ../src/lsp/server.bend as Server
import ../src/lsp/proto.bend as Proto
import ../src/lsp/enc.bend as Enc
import ../laws/LspPositionsUseNegotiatedEncoding.bend as Laws
import ./lemmas/BoolEmptiness.bend as M1

# positions
# ---------

# the cells of the encodings offered say utf-32 exactly when the list has it
law nav.offers_contains:
  for xs: List<&2, String>
  {Enc.offers(Enc.cells(Ezjson.arr(Proto.strings(xs)))) == List.contains(~String, ~String.eq, xs, "utf-32") : Bool}

# Bool.or is List.contains's step (List.any.if, bend 2.0.37) on a rest already
# computed
law nav.or_if:
  for b: Bool
  for -r: Bool
  {Bool.or(b, r) == List.any.if(_u => r, b) : Bool}

def nav.or_if(b, _r):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def nav.offers_contains(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      Equal.trans(Bool,
        Bool.or(String.eq(x, "utf-32"), Enc.offers(Enc.cells(Ezjson.arr(Proto.strings(t))))),
        Bool.or(String.eq(x, "utf-32"), List.contains(~String, ~String.eq, t, "utf-32")),
        List.any.if(_u => List.contains(~String, ~String.eq, t, "utf-32"), String.eq(x, "utf-32")),
        Equal.cong(Bool, Bool, r => Bool.or(String.eq(x, "utf-32"), r),
          Enc.offers(Enc.cells(Ezjson.arr(Proto.strings(t)))),
          List.contains(~String, ~String.eq, t, "utf-32"), nav.offers_contains(t)),
        nav.or_if(String.eq(x, "utf-32"), List.contains(~String, ~String.eq, t, "utf-32")))

def Laws.enc_negotiated(xs):
  Equal.cong(Bool, Enc.Enc, Enc.chosen, Enc.offers(Enc.cells(Ezjson.arr(Proto.strings(xs)))),
    List.contains(~String, ~String.eq, xs, "utf-32"), nav.offers_contains(xs))

def Laws.enc_advertised(_params):
  {==}

def Laws.enc_kept(mm, h, _params, _ee):
  match mm:
    case Server.MInitialize{}:
      Empty.absurd({Server.encoding(Server.MInitialize{}, _params, _ee) == _ee : Enc.Enc}, M1.true_false(h))
    case Server.MShutdown{}:
      {==}
    case Server.MExit{}:
      {==}
    case Server.MOpen{}:
      {==}
    case Server.MChange{}:
      {==}
    case Server.MSave{}:
      {==}
    case Server.MClose{}:
      {==}
    case Server.MHover{}:
      {==}
    case Server.MDefinition{}:
      {==}
    case Server.MSymbols{}:
      {==}
    case Server.MCompletion{}:
      {==}
    case Server.MReferences{}:
      {==}
    case Server.MRename{}:
      {==}
    case Server.MSemantic{}:
      {==}
    case Server.MOther{}:
      {==}

# a char and the ones after it, counted and read back, whatever its width
law nav.round_char:
  for -c: Char
  for -t: List<&2, Char>
  for -p: Nat
  for b: Bool
  for h: {Enc.wide(c) == b : Bool}
  for ih: {Enc.points(t, Enc.units(t, p)) == p : Nat}
  {Enc.points(Con{c, t}, Enc.units(Con{c, t}, 1n+p)) == 1n+p : Nat}

def nav.round_char(c, t, p, b, h, ih):
  match b:
    case True{}:
      +h2 = Equal.sym(Bool, Enc.wide(c), True{}, h)
      %h2 : {Enc.points(Con{c, t}, Enc.units.step(_, Enc.units(t, p))) == 1n+p : Nat}
      %h2 : {1n+Enc.points(t, Enc.points.skip(_, 1n+Enc.units(t, p))) == 1n+p : Nat}
      Equal.cong(Nat, Nat, x => 1n+x, Enc.points(t, Enc.units(t, p)), p, ih)
    case False{}:
      +h2 = Equal.sym(Bool, Enc.wide(c), False{}, h)
      %h2 : {Enc.points(Con{c, t}, Enc.units.step(_, Enc.units(t, p))) == 1n+p : Nat}
      %h2 : {1n+Enc.points(t, Enc.points.skip(_, Enc.units(t, p))) == 1n+p : Nat}
      Equal.cong(Nat, Nat, x => 1n+x, Enc.points(t, Enc.units(t, p)), p, ih)

# UTF-16 code units read back as code points are the code points counted
law nav.round16:
  for cs: List<&2, Char>
  for nn: Nat
  {Enc.points(cs, Enc.units(cs, nn)) == nn : Nat}

def nav.round16(cs, nn):
  match cs:
    case Nil{}:
      {==}
    case Con{c, t}:
      match nn:
        case 0n:
          {==}
        case 1n+p:
          nav.round_char(c, t, p, Enc.wide(c), {==}, nav.round16(t, p))

def Laws.enc_round(ee, cs, nn):
  match ee:
    case Enc.Utf16{}:
      nav.round16(cs, nn)
    case Enc.Utf32{}:
      {==}

def Laws.enc_sent(_cc, _line, _ch):
  {==}

def Laws.enc_read(_cc, _params):
  {==}

def Laws.enc_tokens(_ee, _cs, _line, _col, _len, _typ):
  {==}

def Laws.enc_utf32(_lines, _line, _col):
  ({==}, {==})
