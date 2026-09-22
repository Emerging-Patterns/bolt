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

# how many UTF-8 bytes the chars take, plus n
def byte_len(cs: List<&2, Char>, nn: U32) -> U32:
  match cs:
    case Nil{}:
      nn
    case Con{c, t}:
      +w = width(Char.to_u32(c))
      byte_len(t, (nn + w : U32))

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

# framing
# -------

# a message on its way out
def wrap(+body: String) -> String:
  "Content-Length: " ++ U32.show(byte_len(String.to_list(body), 0)) ++ "\r\n\r\n" ++ body

# the header block's Content-Length and the bytes after it, once it is whole
type Head is Data:
  NoHead{}
  Head{len: U32, rest: List<&2, U32>}

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
def line_len(line: List<&2, U32>, +len: U32) -> U32:
  +s = String.from_list(chars(line, []))
  Bool.pick(U32, String.starts_with(s, "Content-Length: "),
    Maybe.default(&2, U32, U32.read(String.drop(s, 16n)), len), len)

# the header block read up to its blank line: Content-Length, and the bytes
# after; not whole yet when the blank line has not come
def header(bs: List<&2, U32>, line: List<&2, U32>, len: U32) -> Head:
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

# the first n bytes (reversed onto acc) and the rest, or not yet when there
# are fewer
def split(nn: Nat, xs: List<&2, U32>, acc: List<&2, U32>) -> Cut:
  match nn xs:
    case 0n rest:
      Ready{List.reverse(&2, U32, acc), rest}
    case 1n+p Nil{}:
      More{}
    case 1n+p Con{h, t}:
      split(p, t, h <> acc)

def cut.body(hh: Head) -> Cut:
  match hh:
    case NoHead{}:
      More{}
    case Head{len, rest}:
      split(U32.to_nat(len), rest, [])

# the front of a buffer: a whole message body and the bytes after it, or
# not yet
def cut(buf: List<&2, U32>) -> Cut:
  cut.body(header(buf, [], 0))
