# lsp/bench/request: the server's pure work for one request, 2^DEPTH times
# over, under a `!` call: the same binary runs it on the cores (`--gpu off`)
# or on the GPU (`--gpu 4GB`). One leaf is what a hover costs the server
# besides IO: parse the message, outline the document, find the word, find
# the item. Prints the checksum, then the milliseconds the fold took (the
# process's start, and the GPU's, are outside that span).
import Base
import ../../syntax/outline.bend as Outline
import ../../syntax/word.bend as Word
import 0xd9c8d4d2899ddda845dfa7525a3568ea/main.bend as Ezjson
import 0xd9c8d4d2899ddda845dfa7525a3568ea/value.bend as J

# the document a hover is answered against
def source() -> String:
  "# a module\nimport Base\nimport ./math.bend as M\n\n# a shape\ntype Shape<-A: Type> is Data:\n  Circle{r: U32}\n  Square{s: U32}\n\n# the area\ndef area(x: Shape) -> U32:\n  match x:\n    case Circle{+r}:\n      (3 * r * r : U32)\n    case Square{+s}:\n      (s * s : U32)\n\ndef long.header(\n  a: U32, b: U32\n) -> U32:\n  area(Square{a})\n\n# LAW: zero is neutral\nlaw add_zero:\n  for x: Nat\n  {Nat.add(x, 0n) == x : Nat}\n\ndef main() -> U32:\n  long.header(area(Circle{2}), 3)"

# the hover request
def message() -> String:
  "{\"jsonrpc\":\"2.0\",\"id\":7,\"method\":\"textDocument/hover\",\"params\":{\"textDocument\":{\"uri\":\"file:///w/app/main.bend\"},\"position\":{\"line\":28,\"character\":17}}}"

# an item's line, 0 when there is none
def line_of(item: Maybe<&2, Outline.Item>) -> U32:
  match item:
    case None{}:
      0
    case Some{Outline.Item{k, name, line, sig, doc, path}}:
      line

# a parsed message, or null
def parsed(mm: Maybe<&2, J.Json>) -> J.Json:
  Maybe.default(&2, J.Json, mm, J.JNull{})

# one request: the line of the item under the message's position, plus its id
def leaf(+ii: U32) -> U32:
  +msg = parsed(Ezjson.parse(message()))
  +pos = Ezjson.get(Ezjson.get(msg, "params"), "position")
  (line_of(Outline.find(Outline.items(source()),
    Word.at(source(), Maybe.default(&2, U32, Ezjson.as_u32(Ezjson.get(pos, "line")), 0),
      Maybe.default(&2, U32, Ezjson.as_u32(Ezjson.get(pos, "character")), 0))))
    + Maybe.default(&2, U32, Ezjson.as_u32(Ezjson.get(msg, "id")), 0) + (ii .&. 0) : U32)

# the requests of a 2^n batch, answered and summed
def fold(+nn: Nat, +ii: U32) -> U32:
  match nn:
    case 0n:
      leaf(ii)
    case 1n+p:
      a b = fold(p, (ii * 2 : U32)) fold(p, (ii * 2 + 1 : U32))
      (a + b : U32)

# DEPTH from the environment: the batch is 2^depth requests
def depth(rr: Result<&1, &1, U32 & String, String>) -> U32:
  match rr:
    case Fail{e}:
      0
    case Done{s}:
      Maybe.default(&2, U32, U32.read(s), 0)

def main() -> IO(Unit):  # noqa: L001 IO entry point
  do IO<Unit>:
    r : Result<&1, &1, U32 & String, String> <- IO.get_env("DEPTH")
    t0 : Nat <- IO.now()
    sum : U32 <- IO.pure(U32, fold!(U32.to_nat(depth(r)), 0))
    IO.print(U32.show(sum))
    t1 : Nat <- IO.now()
    IO.print(Nat.show(Nat.sub(t1, t0)))
