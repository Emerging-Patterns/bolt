# bolt/lsp: the laws. LSP's framing (frame.bend) is pure, so these quantify
# over every message body, every byte that follows it on the wire, and every
# point a read may stop at.
import Base
import ./frame.bend as Frame

# a digit as its char
def digit_char(dd: Frame.Digit) -> Char:
  match dd:
    case Frame.D0{}:
      '0'
    case Frame.D1{}:
      '1'
    case Frame.D2{}:
      '2'
    case Frame.D3{}:
      '3'
    case Frame.D4{}:
      '4'
    case Frame.D5{}:
      '5'
    case Frame.D6{}:
      '6'
    case Frame.D7{}:
      '7'
    case Frame.D8{}:
      '8'
    case Frame.D9{}:
      '9'

# a digit's value
def digit_value(dd: Frame.Digit) -> Nat:
  match dd:
    case Frame.D0{}:
      0n
    case Frame.D1{}:
      1n
    case Frame.D2{}:
      2n
    case Frame.D3{}:
      3n
    case Frame.D4{}:
      4n
    case Frame.D5{}:
      5n
    case Frame.D6{}:
      6n
    case Frame.D7{}:
      7n
    case Frame.D8{}:
      8n
    case Frame.D9{}:
      9n

# ten times n
def tens(nn: Nat) -> Nat:
  match nn:
    case 0n:
      0n
    case 1n+p:
      Nat.add(10n, tens(p))

# a count's value: its digits, least significant first, in base ten
def value(ds: List<&2, Frame.Digit>) -> Nat:
  match ds:
    case Nil{}:
      0n
    case Con{d, t}:
      Nat.add(digit_value(d), tens(value(t)))

# a count as text, most significant digit first
def digits(ds: List<&2, Frame.Digit>) -> String:
  match ds:
    case Nil{}:
      ""
    case Con{d, t}:
      digits(t) ++ SCon{digit_char(d), SNil{}}

# the bytes wrap(s) puts on the wire
def wire(ss: String) -> List<&2, U32>:
  Frame.encode(Frame.wrap(ss))

# LAW: Content-Length counts UTF-8 bytes: wrap heads the body with the
# decimal text of a count whose value is the number of bytes the body takes
# in UTF-8
# BOLT-LSP-1
law frame_counts:
  for +s: String
  exs ds: List<&2, Frame.Digit>
  {Frame.wrap(s) == "Content-Length: " ++ digits(ds) ++ "\r\n\r\n" ++ s : String}
    & {value(ds) == List.length(&2, U32, Frame.encode(s)) : Nat}

# LAW: cut of wrap(s) gives s: cut of the wire, whatever follows it, is the
# body's bytes and then the bytes that follow
# BOLT-LSP-1
law frame_round:
  for +s: String
  for more: List<&2, U32>
  {Frame.cut(List.append(&2, U32, wire(s), more)) == Frame.Ready{Frame.encode(s), more} : Frame.Cut}

# LAW: a partial header or body waits: cut of every proper prefix of the wire
# is not yet a message
# BOLT-LSP-1
law frame_waits:
  for +s: String
  for kk: Nat
  for h: {Nat.is_lt(kk, List.length(&2, U32, wire(s))) == True{} : Bool}
  {Frame.cut(List.take(&2, U32, wire(s), kk)) == Frame.More{} : Frame.Cut}
