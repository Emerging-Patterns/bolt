# lsp/enc: position encodings (LSP 3.17 `positionEncoding`), the one place a
# character offset crosses the protocol boundary. Pure. bolt counts columns in
# code points (a Bend String is a list of them); a client that offers
# `utf-32` gets exactly those, and any other gets UTF-16 code units, where a
# char outside the Basic Multilingual Plane counts 2. Every position the
# server reads goes through `into`, and every one it sends through `out`
# (proto.bend's position, semantic.bend's tokens).
import Base
import 0xd9c8d4d2899ddda845dfa7525a3568ea/value.bend as J

# the encodings the server speaks
type Enc is Data:
  Utf16{}
  Utf32{}

# an encoding's name on the wire
def name(ee: Enc) -> String:
  match ee:
    case Utf16{}:
      "utf-16"
    case Utf32{}:
      "utf-32"

# does a list of encodings (JSON cells) offer utf-32? A cell that is not a
# string offers nothing
def offers(cells: J.Json) -> Bool:
  match cells:
    case J.JCons{h, t}:
      +more = offers(t)
      Bool.or(String.eq(Maybe.default(&2, String, J.as_str(h), ""), "utf-32"), more)
    case _other:
      False{}

# the cells of an array, JNil when it is not one
def cells(jj: J.Json) -> J.Json:
  match jj:
    case J.JArr{items}:
      items
    case _other:
      J.JNil{}

# the encoding for utf-32 offered or not
def chosen(yes: Bool) -> Enc:
  match yes:
    case True{}:
      Utf32{}
    case False{}:
      Utf16{}

# the encoding initialize settles on: utf-32 when the client's
# general.positionEncodings offers it, else UTF-16, LSP's default
def negotiate(params: J.Json) -> Enc:
  chosen(offers(cells(J.get(J.get(J.get(params, "capabilities"), "general"), "positionEncodings"))))

# counting
# --------

# does a char take two UTF-16 code units (it lies past U+FFFF)?
def wide(cc: Char) -> Bool:
  U32.is_le(65536, Char.to_u32(cc))

# the units a char and the ones after it take: two for a wide char, else one
def units.step(isw: Bool, rest: Nat) -> Nat:
  match isw:
    case True{}:
      2n+rest
    case False{}:
      1n+rest

# the UTF-16 code units the first n chars of a line take; a column past the
# line's end counts one unit a column
def units(cs: List<&2, Char>, nn: Nat) -> Nat:
  match cs nn:
    case Nil{} _:
      nn
    case Con{_c, _t} 0n:
      0n
    case Con{c, t} 1n+p:
      units.step(wide(c), units(t, p))

# the units left after a char, from 1+p units: p after a narrow one, one
# fewer after a wide one (none when the offset falls inside its pair)
def points.skip(isw: Bool, pp: Nat) -> Nat:
  match isw pp:
    case True{} 0n:
      0n
    case True{} 1n+q:
      q
    case False{} _:
      pp

# the chars the first u UTF-16 code units of a line cover; an offset inside
# a pair covers its char, and one past the line's end counts one column a
# unit
def points(cs: List<&2, Char>, uu: Nat) -> Nat:
  match cs uu:
    case Nil{} _:
      uu
    case Con{_c, _t} 0n:
      0n
    case Con{c, t} 1n+p:
      1n+points(t, points.skip(wide(c), p))

# a code-point column of a line in an encoding
def out.of(ee: Enc, cs: List<&2, Char>, nn: Nat) -> Nat:
  match ee:
    case Utf16{}:
      units(cs, nn)
    case Utf32{}:
      nn

# an encoding's column of a line as a code-point column
def into.of(ee: Enc, cs: List<&2, Char>, uu: Nat) -> Nat:
  match ee:
    case Utf16{}:
      points(cs, uu)
    case Utf32{}:
      uu

# a document as the boundary sees it: the encoding and the text's lines
type Cols is Data:
  Cols{enc: Enc, lines: List<&2, String>}

# a document's text under an encoding
def cols(ee: Enc, text: String) -> Cols:
  Cols{ee, String.lines(text)}

# a line's chars, none past the end
def chars(lines: List<&2, String>, line: U32) -> List<&2, Char>:
  String.to_list(Maybe.default(&2, String, List.get(&2, String, lines, U32.to_nat(line)), ""))

# a code-point column of a line's chars, sent in an encoding
def out.col(ee: Enc, cs: List<&2, Char>, col: U32) -> U32:
  match ee:
    case Utf16{}:
      U32.from_nat(out.of(Utf16{}, cs, U32.to_nat(col)))
    case Utf32{}:
      col

# a code-point column sent in the negotiated encoding
def out(cc: Cols, line: U32, col: U32) -> U32:
  Cols{ee, lines} = cc
  out.col(ee, chars(lines, line), col)

# a column of a line's chars read in an encoding, as a code-point column
def into.col(ee: Enc, cs: List<&2, Char>, col: U32) -> U32:
  match ee:
    case Utf16{}:
      U32.from_nat(into.of(Utf16{}, cs, U32.to_nat(col)))
    case Utf32{}:
      col

# a column read in the negotiated encoding, as a code-point column
def into(cc: Cols, line: U32, col: U32) -> U32:
  Cols{ee, lines} = cc
  into.col(ee, chars(lines, line), col)
