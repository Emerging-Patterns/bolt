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

# LAW: a char takes two UTF-16 code units exactly when its code point is
# U+10000 (65536) or above: the first one past the Basic Multilingual Plane
# is itself two units
law wide_from_u10000:
  for +xx: U32
  {Enc.wide(Chr{xx}) == U32.is_le(65536, xx) : Bool}

# LAW: a UTF-16 document that holds such a char on some line keeps
# converting as UTF-16
law narrowed_keeps_utf16_with_a_wide_char:
  for +lines: List<&2, String>
  for e: {Enc.wide_any(lines) == True{} : Bool}
  {Enc.narrowed(Enc.Utf16{}, Enc.wide_any(lines)) == Enc.Utf16{} : Enc.Enc}

# LAW: one that holds none converts as utf-32, which counts the same there
law narrowed_reads_utf16_as_utf32_without_one:
  for +lines: List<&2, String>
  for e: {Enc.wide_any(lines) == False{} : Bool}
  {Enc.narrowed(Enc.Utf16{}, Enc.wide_any(lines)) == Enc.Utf32{} : Enc.Enc}

# LAW: a utf-32 document converts as utf-32 whatever it holds
law narrowed_keeps_utf32:
  for wide: Bool
  {Enc.narrowed(Enc.Utf32{}, wide) == Enc.Utf32{} : Enc.Enc}
