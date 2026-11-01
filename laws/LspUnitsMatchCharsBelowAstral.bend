# On a line with no character past U+FFFF, a column counted in UTF-16 units
# equals the column counted in characters, both sent and read.
import Base
import ../src/lsp/enc.bend as Enc

# LAW: on a line with no char past U+FFFF, a column counted in UTF-16 units
# equals the column counted in characters, both ways: why Enc.cols converts
# such a document as utf-32
law enc_narrow:
  for +lines: List<&2, String>
  for h: {Enc.wide_any(lines) == False{} : Bool}
  for +line: U32
  for +nn: Nat
  {Enc.out.of(Enc.Utf16{}, Enc.chars(lines, line), nn) == nn : Nat}
    & {Enc.into.of(Enc.Utf16{}, Enc.chars(lines, line), nn) == nn : Nat}
