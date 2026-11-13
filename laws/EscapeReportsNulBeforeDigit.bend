# `escape` reports exactly one finding for each `\0` followed by a digit in a
# string or char literal, its escapes read as a backslash and the one char
# after it, and none for anything else. A finding with digits after the
# `\0` names the fix: the code point of the one or two octal digits that
# follow (`\033` is `\u{1B}`), in hex.
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/rules/correctness/escape.bend as Esc

# 1 when the Syms open with a digit (`0` included), else 0
def nul_lead(ss: List<&2, Esc.Sym>) -> Nat:
  match ss:
    case Con{Esc.SZero{}, t}:
      1n
    case Con{Esc.SDigit{d}, t}:
      1n
    case other:
      0n

# how many `\0`s a literal holds with a digit right after, its escapes read
# as Bend reads them: a backslash and the one char after it
def nul_count(ss: List<&2, Esc.Sym>) -> Nat:
  match ss:
    case Con{Esc.SSlash{}, Con{Esc.SZero{}, +rest}}:
      Nat.add(nul_lead(rest), nul_count(rest))
    case Con{Esc.SSlash{}, Con{e, rest}}:
      nul_count(rest)
    case Con{s, rest}:
      nul_count(rest)
    case Nil{}:
      0n

# how many such escapes the string and char literals among the tokens hold
def esc_count(toks: List<&2, Lex.Tok>) -> Nat:
  match toks:
    case Con{Lex.Tok{Lex.TStr{}, t, l, c}, rest}:
      Nat.add(nul_count(Esc.syms(String.to_list(t))), esc_count(rest))
    case Con{Lex.Tok{Lex.TChar{}, t, l, c}, rest}:
      Nat.add(nul_count(Esc.syms(String.to_list(t))), esc_count(rest))
    case Con{h, rest}:
      esc_count(rest)
    case Nil{}:
      0n

# LAW: escape reports one finding for each `\0` then a digit in a literal,
# its escapes read a backslash and one char at a time, and none elsewhere in it
law escape_scan_counts:
  for ss: List<&2, Esc.Sym>
  for +path: String
  for +line: U32
  for +col: U32
  {List.length(&2, F.Finding, Esc.scan(ss, path, line, col)) == nul_count(ss) : Nat}

# LAW: escape reports exactly those escapes of the string and char literals,
# and nothing for any other token: a comment or code never has one
law escape_counts:
  for toks: List<&2, Lex.Tok>
  for +path: String
  {List.length(&2, F.Finding, Esc.check.go(toks, path)) == esc_count(toks) : Nat}

# Law vocabulary for the fix the message suggests: an octal digit, a decimal
# digit after `0`, and the code point of each escape written out in hex.

# an octal digit's value
type Oct is Data:
  O0{}
  O1{}
  O2{}
  O3{}
  O4{}
  O5{}
  O6{}
  O7{}

# a decimal digit other than `0`
type Dig is Data:
  D1{}
  D2{}
  D3{}
  D4{}
  D5{}
  D6{}
  D7{}
  D8{}
  D9{}

# an octal digit's value
def oct.n(dd: Oct) -> Nat:
  match dd:
    case O0{}:
      0n
    case O1{}:
      1n
    case O2{}:
      2n
    case O3{}:
      3n
    case O4{}:
      4n
    case O5{}:
      5n
    case O6{}:
      6n
    case O7{}:
      7n

# an octal digit's char
def oct.char(dd: Oct) -> Char:
  match dd:
    case O0{}:
      '0'
    case O1{}:
      '1'
    case O2{}:
      '2'
    case O3{}:
      '3'
    case O4{}:
      '4'
    case O5{}:
      '5'
    case O6{}:
      '6'
    case O7{}:
      '7'

# a decimal digit's char
def dig.char(dd: Dig) -> Char:
  match dd:
    case D1{}:
      '1'
    case D2{}:
      '2'
    case D3{}:
      '3'
    case D4{}:
      '4'
    case D5{}:
      '5'
    case D6{}:
      '6'
    case D7{}:
      '7'
    case D8{}:
      '8'
    case D9{}:
      '9'

# is a decimal digit an octal one?
def dig.octal(dd: Dig) -> Bool:
  match dd:
    case D1{}:
      True{}
    case D2{}:
      True{}
    case D3{}:
      True{}
    case D4{}:
      True{}
    case D5{}:
      True{}
    case D6{}:
      True{}
    case D7{}:
      True{}
    case D8{}:
      False{}
    case D9{}:
      False{}

# the code points 0 to 63 (all a one or two digit octal escape can name),
# spelled in hex as the message writes them
def hex.names() -> List<&2, String>:
  ["0", "1", "2", "3", "4", "5", "6", "7", "8", "9", "A", "B", "C", "D", "E", "F", "10", "11",
   "12", "13", "14", "15", "16", "17", "18", "19", "1A", "1B", "1C", "1D", "1E", "1F", "20", "21",
   "22", "23", "24", "25", "26", "27", "28", "29", "2A", "2B", "2C", "2D", "2E", "2F", "30", "31",
   "32", "33", "34", "35", "36", "37", "38", "39", "3A", "3B", "3C", "3D", "3E", "3F"]

# a name from the table; past its end, nothing
def hex.at(mm: Maybe<&2, String>) -> String:
  match mm:
    case None{}:
      ""
    case Some{nm}:
      nm

# a code point's name from the table
def hex.named(nn: Nat) -> String:
  hex.at(List.get(&2, String, hex.names(), nn))

# LAW: after `\0`, a decimal digit is read as part of the escape exactly when
# it is an octal digit, `1` to `7`
law escape_octal_digits:
  for dd: Dig
  {Esc.octal(Esc.SDigit{dig.char(dd)})
    == Bool.pick(Maybe<&2, Char>, dig.octal(dd), Some{dig.char(dd)}, None{}) : Maybe<&2, Char>}

# LAW: the fix for `\0a` names code point a, in hex
law escape_names_one_digit:
  for aa: Oct
  {Esc.hex(Esc.value([oct.char(aa)], 0)) == hex.named(oct.n(aa)) : String}

# LAW: the fix for `\0ab` names code point 8a + b, in hex: `\033` is `\u{1B}`
law escape_names_two_digits:
  for aa: Oct
  for bb: Oct
  {Esc.hex(Esc.value([oct.char(aa), oct.char(bb)], 0)) == hex.named(Nat.add(Nat.mul(oct.n(aa), 8n), oct.n(bb)))
    : String}
