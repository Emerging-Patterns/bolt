# syntax/outline: the top-level items of a source, tolerant of what it
# does not understand
import Base
import ../outline.bend as Outline
import ../../wire/check/kit.bend as Check
import ../../wire/check/print.bend as Report

def source() -> String:
  String.join([
    "# a module",
    "import Base",
    "import ./math.bend as M",
    "",
    "# a shape",
    "# in two lines",
    "type Shape<-A: Type> is Data:",
    "  Circle{r: U32}",
    "  Square{s: U32}",
    "",
    "stray junk here (((",
    "# the area",
    "def area(x: Shape) -> U32:",
    "  match x:",
    "    case Circle{+r}:",
    "      (3 * r : U32)",
    "",
    "def long.header(",
    "  a: U32, b: U32",
    ") -> U32:",
    "  a",
    "",
    "# LAW: zero is neutral",
    "law add_zero:",
    "  for x: Nat",
    "  {Nat.add(x, 0n) == x : Nat}",
    "@unsafe def spin(x: U32) -> U32:",
    "  spin(x)"], "\n")

def kind(k: Outline.ItemKind) -> String:
  match k:
    case Outline.IImport{}:
      "import"
    case Outline.IDef{}:
      "def"
    case Outline.ILaw{}:
      "law"
    case Outline.IType{}:
      "type"
    case Outline.ICtor{}:
      "ctor"
    case Outline.ILocal{}:
      "local"

def show.go(items: List<&2, Outline.Item>) -> List<&2, String>:
  match items:
    case Nil{}:
      Nil{}
    case Con{Outline.Item{k, name, line, sig, doc, path}, t}:
      (kind(k) ++ " " ++ name ++ " @" ++ U32.show(line) ++ " <" ++ path ++ "> [" ++ doc ++ "] " ++ sig) <> show.go(t)

def main() -> IO(Unit):
  IO.print(String.join(show.go(Outline.items(source())), "\n"))

#|import Base @1 <Base> [a module] import Base
#|import M @2 <./math.bend> [] import ./math.bend as M
#|type Shape @6 <> [a shape
#|in two lines] type Shape<-A: Type> is Data:
#|ctor Circle @7 <> [] Circle{r: U32}
#|ctor Square @8 <> [] Square{s: U32}
#|def area @12 <> [the area] def area(x: Shape) -> U32:
#|def long.header @17 <> [] def long.header(
#|  a: U32, b: U32
#|) -> U32:
#|law add_zero @23 <> [LAW: zero is neutral] law add_zero:
#|  for x: Nat
#|  {Nat.add(x, 0n) == x : Nat}
#|def spin @26 <> [] @unsafe def spin(x: U32) -> U32:
