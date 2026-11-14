# Positions are in the encoding the client negotiated.
import Base
import ezjson@1.2.0.0/main.bend as Ezjson
import ezjson@1.2.0.0/src/value.bend as J
import ../src/lsp/server.bend as Server
import ../src/lsp/proto.bend as Proto
import ../src/lsp/enc.bend as Enc
import ../src/lsp/semantic.bend as Semantic

# positions
# ---------

# bolt counts columns in code points. initialize settles the encoding
# (utf-32 when the client offers it, else UTF-16), the loop keeps it, and
# enc.bend is the one place a column crosses the boundary: every position
# the server sends is built by Proto.position, which sends its character
# through Enc.out, and every one it reads is Server.col_in, through
# Enc.into; semantic tokens send each column and length through
# Enc.out.col. Under UTF-16 a char past U+FFFF counts two units.

# the initialize params of a client that lists these position encodings
def nav.offered(xs: List<&2, String>) -> J.Json:
  Ezjson.obj([("capabilities", Ezjson.obj([("general", Ezjson.obj([("positionEncodings",
      Ezjson.arr(Proto.strings(xs)))]))]))])

# LAW: initialize settles on utf-32 exactly when the client offers it, and
# on UTF-16 otherwise
law enc_negotiated:
  for +xs: List<&2, String>
  {Enc.negotiate(nav.offered(xs)) == Enc.chosen(List.contains(~String, ~String.eq, xs, "utf-32")) : Enc.Enc}

# LAW: initialize's reply names the encoding it settled on
law enc_advertised:
  for +params: J.Json
  {Ezjson.get(Ezjson.get(Proto.capabilities(Server.encoding(Server.MInitialize{}, params, Enc.Utf16{})),
      "capabilities"),
    "positionEncoding") == J.JStr{Enc.name(Enc.negotiate(params))} : J.Json}

# is this method initialize?
def nav.is_init(m: Server.Method) -> Bool:
  match m:
    case Server.MInitialize{}:
      True{}
    case _other:
      False{}

# LAW: every message but initialize leaves the encoding as it was
law enc_kept:
  for m: Server.Method
  for h: {nav.is_init(m) == False{} : Bool}
  for params: J.Json
  for +e: Enc.Enc
  {Server.encoding(m, params, e) == e : Enc.Enc}

# LAW: the helper round-trips: a code-point column sent in an encoding and
# read back in it is the same column, on every line
law enc_round:
  for +e: Enc.Enc
  for +cs: List<&2, Char>
  for n: Nat
  {Enc.into.of(e, cs, Enc.out.of(e, cs, n)) == n : Nat}

# LAW: every position the server sends carries its character in the
# negotiated encoding
law enc_sent:
  for +c: Enc.Cols
  for +line: U32
  for ch: U32
  {Proto.position(c, line, ch) == Proto.position.at(line, Enc.out(c, line, ch)) : J.Json}

# LAW: every position the server reads is read in the negotiated encoding
law enc_read:
  for c: Enc.Cols
  for +params: J.Json
  {Server.col_in(c, params) == Enc.into(c, Server.line_of(params), Server.col_of(params)) : U32}

# LAW: every semantic token's column and length are sent in the negotiated
# encoding
law enc_tokens:
  for +e: Enc.Enc
  for +cs: List<&2, Char>
  for line: U32
  for +col: U32
  for +len: U32
  for typ: U32
  {Semantic.sent.one(e, cs, Semantic.Sem{line, col, len, typ})
    == Semantic.Sem{line, Enc.out.col(e, cs, col),
      (Enc.out.col(e, cs, (col + len : U32)) - Enc.out.col(e, cs, col) : U32), typ} : Semantic.Sem}

# LAW: in utf-32 a column crosses the boundary unchanged
law enc_utf32:
  for lines: List<&2, String>
  for line: U32
  for +col: U32
  {Enc.out(Enc.Cols{Enc.Utf32{}, lines}, line, col) == col : U32}
    & {Enc.into(Enc.Cols{Enc.Utf32{}, lines}, line, col) == col : U32}
