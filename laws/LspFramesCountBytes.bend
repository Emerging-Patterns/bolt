# `Content-Length` counts UTF-8 bytes; a partial header or body waits; `cut`
# of `wrap(s)` gives `s`.
import Base
import ../src/lsp/frame.bend as Frame

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
law frame_counts:
  for +s: String
  exs ds: List<&2, Frame.Digit>
  {Frame.wrap(s) == "Content-Length: " ++ digits(ds) ++ "\r\n\r\n" ++ s : String}
    & {value(ds) == List.length(&2, U32, Frame.encode(s)) : Nat}

# LAW: cut of wrap(s) gives s: cut of the wire, whatever follows it, is the
# body's bytes and then the bytes that follow
law frame_round:
  for +s: String
  for more: List<&2, U32>
  {Frame.cut(List.append(&2, U32, wire(s), more)) == Frame.Whole{Frame.encode(s), more} : Frame.Cut}

# LAW: a partial header or body waits: cut of every proper prefix of the wire
# is not yet a message
law frame_waits:
  for +s: String
  for kk: Nat
  for h: {Nat.is_lt(kk, List.length(&2, U32, wire(s))) == True{} : Bool}
  {Frame.cut(List.take(&2, U32, wire(s), kk)) == Frame.More{} : Frame.Cut}

# What the transport reads next (Frame.next). bend's File.read_bytes waits
# until it has all it was asked for, so a server that asks for more than the
# message in hand waits for bytes the editor will not send until it has its
# answer. The transport therefore asks for a header line while the header
# block has not ended, and after that for what the body still lacks, held to
# 65536 a read and never none.

# LAW: while the header block has not ended, the next read is a line
law next_reads_a_header_line:
  for buf: List<&2, U32>
  for e: {Frame.header(buf, [], [Frame.D0{}]) == Frame.NoHead{} : Frame.Head}
  {Frame.next(buf) == Frame.Line{} : Frame.Next}

# LAW: once it has, the next read is the bytes the body lacks: its
# Content-Length less the bytes held past the header, held to 65536, and one
# when that is none
law next_reads_what_the_body_lacks:
  for buf: List<&2, U32>
  for len: List<&2, Frame.Digit>
  for rest: List<&2, U32>
  for e: {Frame.header(buf, [], [Frame.D0{}]) == Frame.Head{len, rest} : Frame.Head}
  {Frame.next(buf) == Frame.Bytes{Frame.at_least_one(Frame.count.held(Frame.lack(rest, len)))} : Frame.Next}

# LAW: each byte held takes one off what the body lacks
law lack_takes_each_byte:
  for h: U32
  for t: List<&2, U32>
  for ds: List<&2, Frame.Digit>
  {Frame.lack(h <> t, ds) == Frame.lack(t, Frame.untick(ds)) : List<&2, Frame.Digit>}

# LAW: with no byte held, the body lacks all of its count
law lack_of_none_held:
  for ds: List<&2, Frame.Digit>
  {Frame.lack(Nil{}, ds) == ds : List<&2, Frame.Digit>}

# LAW: a digit's value is its char's code less the code of `0`
law digit_value_is_its_char:
  for dd: Frame.Digit
  {(Frame.digit.value(dd) + 48 : U32) == Frame.digit.code(dd) : U32}

# LAW: a number past 65536 is held to it
law held_caps:
  for +nn: U32
  for e: {U32.is_gt(nn, 65536) == True{} : Bool}
  {Frame.held(nn) == 65536 : U32}

# LAW: any other number is itself
law held_keeps:
  for +nn: U32
  for e: {U32.is_gt(nn, 65536) == False{} : Bool}
  {Frame.held(nn) == nn : U32}

# LAW: a count is read least significant digit first, each digit plus ten
# times the rest, held at every step
law count_held_by_digits:
  for d: Frame.Digit
  for t: List<&2, Frame.Digit>
  {Frame.count.held(d <> t) == Frame.held((Frame.digit.value(d) + 10 * Frame.count.held(t) : U32)) : U32}

# LAW: a count of one digit is that digit's value
law count_held_one_digit:
  for d: Frame.Digit
  {Frame.count.held(d <> Nil{}) == Frame.digit.value(d) : U32}

# LAW: a read never asks for no bytes: none is asked as one
law at_least_one_of_none:
  for +nn: U32
  for e: {U32.is_eq(nn, 0) == True{} : Bool}
  {Frame.at_least_one(nn) == 1 : U32}

# LAW: any other number of bytes is asked as it is
law at_least_one_keeps:
  for +nn: U32
  for e: {U32.is_eq(nn, 0) == False{} : Bool}
  {Frame.at_least_one(nn) == nn : U32}
