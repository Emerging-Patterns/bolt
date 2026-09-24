# lsp/frame: LSP's base protocol, purely: `Content-Length: N\r\n\r\n` and then
# N bytes of UTF-8. Framing counts bytes and a read may end inside a char, so
# the transport reads bytes, cuts on bytes, and only then decodes.
import Base

# UTF-8, bytes to chars
# ---------------------

# the decoder's state: continuation bytes still owed, the code point so far,
# the chars so far (reversed)
type Dec is Data:
  Dec{need: Nat, acc: U32, out: List<&2, Char>}

# a lead byte, by its high nibble; a stray continuation byte stands for itself
def decode.lead(hi: U32, +bb: U32, out: List<&2, Char>) -> Dec:
  match hi:
    case 12:
      Dec{1n, (bb .&. 31 : U32), out}
    case 13:
      Dec{1n, (bb .&. 31 : U32), out}
    case 14:
      Dec{2n, (bb .&. 15 : U32), out}
    case 15:
      Dec{3n, (bb .&. 7 : U32), out}
    case other:
      Dec{0n, 0, Char.from_u32(bb) <> out}

def decode.more(left: Nat, +acc: U32, out: List<&2, Char>) -> Dec:
  match left:
    case 0n:
      Dec{0n, 0, Char.from_u32(acc) <> out}
    case 1n+p:
      Dec{1n+p, acc, out}

def decode.step(+bb: U32, st: Dec) -> Dec:
  Dec{need, acc, out} = st
  match need:
    case 0n:
      decode.lead((bb >> 4n : U32), bb, out)
    case 1n+p:
      decode.more(p, ((acc << 6n) .|. (bb .&. 63) : U32), out)

def decode.run(bs: List<&2, U32>, st: Dec) -> Dec:
  match bs:
    case Nil{}:
      st
    case Con{b, t}:
      decode.run(t, decode.step(b, st))

def decode.end(st: Dec) -> String:
  Dec{need, acc, out} = st
  String.from_list(List.reverse(&2, Char, out))

# UTF-8 bytes as a string (a bad byte is skipped)
def decode(bs: List<&2, U32>) -> String:
  decode.end(decode.run(bs, Dec{0n, 0, []}))

# UTF-8, chars to bytes
# ---------------------

# how many bytes a code point takes
def width(+xx: U32) -> U32:
  Bool.pick(U32, U32.is_lt(xx, 128), 1,
    Bool.pick(U32, U32.is_lt(xx, 2048), 2,
      Bool.pick(U32, U32.is_lt(xx, 65536), 3, 4)))

# a code point's bytes, by its width, in front of the rest
def encode.char(ww: U32, +xx: U32, rest: List<&2, U32>) -> List<&2, U32>:
  match ww:
    case 1:
      xx <> rest
    case 2:
      (192 .|. (xx >> 6n) : U32) <> (128 .|. (xx .&. 63) : U32) <> rest
    case 3:
      (224 .|. (xx >> 12n) : U32) <> (128 .|. ((xx >> 6n) .&. 63) : U32) <> (128 .|. (xx .&. 63) : U32) <> rest
    case other:
      (240 .|. (xx >> 18n) : U32) <> (128 .|. ((xx >> 12n) .&. 63) : U32) <> (128 .|. ((xx >> 6n) .&. 63) : U32)
        <> (128 .|. (xx .&. 63) : U32) <> rest

def encode.one(+xx: U32, rest: List<&2, U32>) -> List<&2, U32>:
  encode.char(width(xx), xx, rest)

def encode.go(cs: List<&2, Char>) -> List<&2, U32>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{c, t}:
      encode.one(Char.to_u32(c), encode.go(t))

# a string as UTF-8 bytes
def encode(ss: String) -> List<&2, U32>:
  encode.go(String.to_list(ss))

# counts in decimal
# -----------------

# Content-Length is a count in decimal. It is kept as its digits, least
# significant first, from writing it to reading it back: neither side goes
# through a U32, whose text round trip would need laws of division by ten on
# 32-bit words, and no length wraps at 2^32 or unfolds into a Nat of its size.

# a decimal digit
type Digit is Data:
  D0{}
  D1{}
  D2{}
  D3{}
  D4{}
  D5{}
  D6{}
  D7{}
  D8{}
  D9{}

# a digit's char code, '0' to '9'
def digit.code(dd: Digit) -> U32:
  match dd:
    case D0{}:
      48
    case D1{}:
      49
    case D2{}:
      50
    case D3{}:
      51
    case D4{}:
      52
    case D5{}:
      53
    case D6{}:
      54
    case D7{}:
      55
    case D8{}:
      56
    case D9{}:
      57

# the digit a char code stands for, if it is one
def digit.read(xx: U32) -> Maybe<&2, Digit>:
  match xx:
    case 48:
      Some{D0{}}
    case 49:
      Some{D1{}}
    case 50:
      Some{D2{}}
    case 51:
      Some{D3{}}
    case 52:
      Some{D4{}}
    case 53:
      Some{D5{}}
    case 54:
      Some{D6{}}
    case 55:
      Some{D7{}}
    case 56:
      Some{D8{}}
    case 57:
      Some{D9{}}
    case other:
      None{}

# a count one more (digits least significant first)
def tick(ds: List<&2, Digit>) -> List<&2, Digit>:
  match ds:
    case Nil{}:
      [D1{}]
    case Con{D0{}, t}:
      D1{} <> t
    case Con{D1{}, t}:
      D2{} <> t
    case Con{D2{}, t}:
      D3{} <> t
    case Con{D3{}, t}:
      D4{} <> t
    case Con{D4{}, t}:
      D5{} <> t
    case Con{D5{}, t}:
      D6{} <> t
    case Con{D6{}, t}:
      D7{} <> t
    case Con{D7{}, t}:
      D8{} <> t
    case Con{D8{}, t}:
      D9{} <> t
    case Con{D9{}, t}:
      D0{} <> tick(t)

# a count plus a char's width in bytes
def tick.by(ww: U32, ds: List<&2, Digit>) -> List<&2, Digit>:
  match ww:
    case 1:
      tick(ds)
    case 2:
      tick(tick(ds))
    case 3:
      tick(tick(tick(ds)))
    case other:
      tick(tick(tick(tick(ds))))

# how many UTF-8 bytes the chars take, counted on from ds
def byte_count(cs: List<&2, Char>, ds: List<&2, Digit>) -> List<&2, Digit>:
  match cs:
    case Nil{}:
      ds
    case Con{c, t}:
      byte_count(t, tick.by(width(Char.to_u32(c)), ds))

# a count's digits, most significant first, in front of acc
def count.show(ds: List<&2, Digit>, acc: String) -> String:
  match ds:
    case Nil{}:
      acc
    case Con{d, t}:
      count.show(t, SCon{Char.from_u32(digit.code(d)), acc})

# is the count zero?
def count.zero(ds: List<&2, Digit>) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case Con{D0{}, t}:
      count.zero(t)
    case Con{d, t}:
      False{}

# a count one less (zero stays zero)
def untick(ds: List<&2, Digit>) -> List<&2, Digit>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{D0{}, t}:
      D9{} <> untick(t)
    case Con{D1{}, t}:
      D0{} <> t
    case Con{D2{}, t}:
      D1{} <> t
    case Con{D3{}, t}:
      D2{} <> t
    case Con{D4{}, t}:
      D3{} <> t
    case Con{D5{}, t}:
      D4{} <> t
    case Con{D6{}, t}:
      D5{} <> t
    case Con{D7{}, t}:
      D6{} <> t
    case Con{D8{}, t}:
      D7{} <> t
    case Con{D9{}, t}:
      D8{} <> t

# one more char's digit onto the count read so far; None once one is no digit
def count.push(md: Maybe<&2, Digit>, acc: Maybe<&2, List<&2, Digit>>) -> Maybe<&2, List<&2, Digit>>:
  match md acc:
    case Some{d} Some{ds}:
      Some{d <> ds}
    case None{} _:
      None{}
    case Some{d} None{}:
      None{}

def count.read.go(ss: String, acc: Maybe<&2, List<&2, Digit>>) -> Maybe<&2, List<&2, Digit>>:
  match ss:
    case SNil{}:
      acc
    case SCon{c, t}:
      count.read.go(t, count.push(digit.read(Char.to_u32(c)), acc))

# a string of digits as a count; None when it is empty or holds anything else
def count.read(ss: String) -> Maybe<&2, List<&2, Digit>>:
  match ss:
    case SNil{}:
      None{}
    case SCon{h, t}:
      count.read.go(SCon{h, t}, Some{[]})

# framing
# -------

# a message on its way out
def wrap(+body: String) -> String:
  "Content-Length: " ++ count.show(byte_count(String.to_list(body), [D0{}]), "") ++ "\r\n\r\n" ++ body

# the header block's Content-Length and the bytes after it, once it is whole
type Head is Data:
  NoHead{}
  Head{len: List<&2, Digit>, rest: List<&2, U32>}

# the front of a buffer: a whole body and the bytes after it, or not yet
type Cut is Data:
  More{}
  Ready{body: List<&2, U32>, rest: List<&2, U32>}

# bytes as chars, one each (for the ASCII header)
def chars(bs: List<&2, U32>, acc: List<&2, Char>) -> List<&2, Char>:
  match bs:
    case Nil{}:
      acc
    case Con{b, t}:
      chars(t, Char.from_u32(b) <> acc)

# a header line (reversed, its \r already dropped) updates the length
def line_len(line: List<&2, U32>, +len: List<&2, Digit>) -> List<&2, Digit>:
  +s = String.from_list(chars(line, []))
  +read = count.read(String.drop(s, 16n))
  Bool.pick(List<&2, Digit>, String.starts_with(s, "Content-Length: "), Maybe.default(&2, List<&2, Digit>, read, len), len)

# the header block read up to its blank line: Content-Length, and the bytes
# after; not whole yet when the blank line has not come
def header(bs: List<&2, U32>, line: List<&2, U32>, len: List<&2, Digit>) -> Head:
  match bs line:
    case Nil{} l:
      NoHead{}
    case Con{10, t} Nil{}:
      Head{len, t}
    case Con{10, t} l:
      header(t, [], line_len(l, len))
    case Con{13, t} l:
      header(t, l, len)
    case Con{c, t} l:
      header(t, c <> l, len)

# the bytes taken so far and the rest once the count is down to zero, else
# what more gives
def split.on(zz: Bool, xs: List<&2, U32>, acc: List<&2, U32>, more: Unit -> Cut) -> Cut:
  match zz:
    case True{}:
      Ready{List.reverse(&2, U32, acc), xs}
    case False{}:
      more(Unit{})

# the first ds bytes (reversed onto acc) and the rest, or not yet when there
# are fewer. The count goes down a digit at a time: never a Nat of its size
def split(xs: List<&2, U32>, +ds: List<&2, Digit>, +acc: List<&2, U32>) -> Cut:
  match xs:
    case Nil{}:
      split.on(count.zero(ds), [], acc, _u => More{})
    case Con{+h, +t}:
      split.on(count.zero(ds), h <> t, acc, _u => split(t, untick(ds), h <> acc))

def cut.body(hh: Head) -> Cut:
  match hh:
    case NoHead{}:
      More{}
    case Head{len, rest}:
      split(rest, len, [])

# the front of a buffer: a whole message body and the bytes after it, or
# not yet
def cut(buf: List<&2, U32>) -> Cut:
  cut.body(header(buf, [], [D0{}]))
