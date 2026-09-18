# syntax/bind: binders, their scopes, and what each name refers to
import Base
import ../bind.bend as Bind
import ../../wire/check/kit.bend as Check
import ../../wire/check/print.bend as Report

def source() -> String:
  String.join([
    "import Base",
    "import ./lex.bend as Lex",
    "",
    "def area(+x: Shape, -A: Type, ~f: U32 -> U32) -> U32:",
    "  match x:",
    "    case Circle{+r}:",
    "      y = (3 * r : U32)",
    "      (a, K{b}) = pair(y)",
    "      g = z => (z + a : U32)",
    "      g(b)",
    "    case Square{s}:",
    "      s",
    "",
    "def main() -> IO(Unit):",
    "  do IO<Unit>:",
    "    name : String <- IO.get_env(\"USER\")",
    "    n : U32 = 3",
    "    n = Lex.step(n)",
    "    IO.print(name)",
    "",
    "law add_zero:",
    "  for x: Nat",
    "  {Nat.add(x, 0n) == x : Nat}",
    "",
    "def long.header(",
    "  first: U32, second: List<&2, U32>",
    ") -> U32:",
    "  area(first)",
    "",
    "type Monoid is Data:",
    "  Monoid{unit: U32, join: @+p:U32 -> @+q:U32 -> U32}"], "\n")

def kind(k: Bind.BindKind) -> String:
  match k:
    case Bind.KItem{}:
      "item"
    case Bind.KCtor{}:
      "ctor"
    case Bind.KParam{}:
      "param"
    case Bind.KTypeParam{}:
      "typeparam"
    case Bind.KField{}:
      "field"
    case Bind.KLocal{}:
      "local"
    case Bind.KPat{}:
      "pat"
    case Bind.KFor{}:
      "for"
    case Bind.KTypeVar{}:
      "typevar"

def names.go(ls: List<&2, Bind.Bind>) -> List<&2, String>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{Bind.Bind{name, line, col, k, note}, t}:
      name <> names.go(t)

def names(line: U32) -> String:
  String.join(names.go(Bind.visible(Bind.bound(source()), line)), " ")

def show_bind(b: Bind.Bind) -> String:
  Bind.Bind{name, line, col, k, note} = b
  U32.show(line) ++ ":" ++ U32.show(col) ++ " " ++ kind(k) ++ " | " ++ note

def show_target(t: Bind.Target) -> String:
  match t:
    case Bind.TLocal{line, col}:
      "local " ++ U32.show(line) ++ ":" ++ U32.show(col)
    case Bind.TItem{name}:
      "item " ++ name
    case Bind.TQual{alias, name}:
      "qual " ++ alias ++ " " ++ name
    case Bind.TFree{}:
      "free"

def site(m: Maybe<&2, Bind.Site>) -> String:
  match m:
    case None{}:
      "-"
    case Some{Bind.SBind{b}}:
      "bind " ++ show_bind(b)
    case Some{Bind.SUse{Bind.Use{name, line, col, t}}}:
      "use " ++ name ++ " -> " ++ show_target(t)

def at(line: U32, col: U32) -> String:
  site(Bind.at(Bind.bound(source()), line, col))

def pair_show(p: Bind.Pos) -> String:
  Bind.Pos{l, c} = p
  U32.show(l) ++ ":" ++ U32.show(c)

def pairs_show(ps: List<&2, Bind.Pos>) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{p, t}:
      pair_show(p) <> pairs_show(t)

def sites(line: U32, col: U32) -> String:
  String.join(pairs_show(Bind.sites(Bind.bound(source()), line, col)), " ")

def item_sites(name: String) -> String:
  String.join(pairs_show(Bind.item_sites(Bind.bound(source()), name)), " ")

def main() -> IO(Unit):
  do IO<Unit>:
    Check.eq_str(~Report.new(), "deep in a case", names(9), "g b a y r f A x")
    Check.eq_str(~Report.new(), "the next case sees none of the first", names(11), "s f A x")
    Check.eq_str(~Report.new(), "do-binds and typed lets", names(18), "n n name")
    Check.eq_str(~Report.new(), "a law's for", names(22), "x")
    Check.eq_str(~Report.new(), "a header over three lines", names(27), "second first")
    Check.eq_str(~Report.new(), "a parameter", at(3, 10), "bind 3:10 param | +x: Shape")
    Check.eq_str(~Report.new(), "a parameter's use", at(4, 8), "use x -> local 3:10")
    Check.eq_str(~Report.new(), "a template parameter's arrow type", at(3, 31), "bind 3:31 param | ~f: U32 -> U32")
    Check.eq_str(~Report.new(), "a case binder", at(5, 17), "bind 5:17 pat | case Circle{+r}:")
    Check.eq_str(~Report.new(), "a destructured let", at(7, 12), "bind 7:12 pat | (a, K{b}) = pair(y)")
    Check.eq_str(~Report.new(), "a constructor in a pattern is a use", at(7, 10), "use K -> free")
    Check.eq_str(~Report.new(), "a lambda's binder", at(8, 16), "use z -> local 8:10")
    Check.eq_str(~Report.new(), "a do-bind", at(15, 4), "bind 15:4 local | name : String <- IO.get_env(\"USER\")")
    Check.eq_str(~Report.new(), "a rebinding reads the old name", at(17, 17), "use n -> local 16:4")
    Check.eq_str(~Report.new(), "a name through an alias", at(17, 8), "use Lex.step -> qual Lex step")
    Check.eq_str(~Report.new(), "a Base name is free", at(18, 4), "use IO.print -> free")
    Check.eq_str(~Report.new(), "an item of the file", at(27, 2), "use area -> item area")
    Check.eq_str(~Report.new(), "a later parameter with type arguments", at(25, 14), "bind 25:14 param | second: List<&2, U32>")
    Check.eq_str(~Report.new(), "a field", at(30, 20), "bind 30:20 field | join: @+p: U32 -> @+q: U32 -> U32")
    Check.eq_str(~Report.new(), "a type variable", at(30, 28), "bind 30:28 typevar | Monoid{unit: U32, join: @+p:U32 -> @+q:U32 -> U32}")
    Check.eq_str(~Report.new(), "nothing at a keyword", at(4, 2), "-")
    Check.eq_str(~Report.new(), "every site of a local", sites(7, 12), "7:12 9:8")
    Check.eq_str(~Report.new(), "every site of an item", item_sites("area"), "3:4 27:2")
    Check.eq_str(~Report.new(), "a constructor line", at(30, 2), "bind 30:2 ctor | Monoid{unit: U32, join: @+p:U32 -> @+q:U32 -> U32}")

#|ok deep in a case
#|ok the next case sees none of the first
#|ok do-binds and typed lets
#|ok a law's for
#|ok a header over three lines
#|ok a parameter
#|ok a parameter's use
#|ok a template parameter's arrow type
#|ok a case binder
#|ok a destructured let
#|ok a constructor in a pattern is a use
#|ok a lambda's binder
#|ok a do-bind
#|ok a rebinding reads the old name
#|ok a name through an alias
#|ok a Base name is free
#|ok an item of the file
#|ok a later parameter with type arguments
#|ok a field
#|ok a type variable
#|ok nothing at a keyword
#|ok every site of a local
#|ok every site of an item
#|ok a constructor line
