# syntax/scope: the parameters and locals visible at a line, innermost first
import Base
import ../scope.bend as Scope
import ../../wire/check/kit.bend as Check
import ../../wire/check/print.bend as Report

def source() -> String:
  String.join([
    "import Base",
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
    "    IO.print(name)",
    "",
    "law add_zero:",
    "  for x: Nat",
    "  {Nat.add(x, 0n) == x : Nat}",
    "",
    "def long.header(",
    "  first: U32, second: List<&2, U32>",
    ") -> U32:",
    "  first"], "\n")

def names.go(ls: List<&2, Scope.Local>) -> List<&2, String>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{Scope.Local{name, line, col, note, param}, t}:
      name <> names.go(t)

def names(line: U32) -> String:
  String.join(names.go(Scope.visible(source(), line)), " ")

def site(m: Maybe<&2, Scope.Local>) -> String:
  match m:
    case None{}:
      "-"
    case Some{Scope.Local{name, line, col, note, param}}:
      U32.show(line) ++ ":" ++ U32.show(col) ++ " " ++ Bool.pick(String, param, "param", "local") ++ " | " ++ note

def look(line: U32, name: String) -> String:
  site(Scope.lookup(source(), line, name))

def main() -> IO(Unit):
  do IO<Unit>:
    Check.eq_str(~Report.new(), "deep in a case", names(8), "g a b y r x A f")
    Check.eq_str(~Report.new(), "a lambda's binder on its own line", names(7), "z g a b y r x A f")
    Check.eq_str(~Report.new(), "the next case sees none of the first", names(10), "s x A f")
    Check.eq_str(~Report.new(), "do-binds and typed lets", names(16), "n name")
    Check.eq_str(~Report.new(), "a law's for", names(20), "x")
    Check.eq_str(~Report.new(), "a header over three lines", names(25), "first second")
    Check.eq_str(~Report.new(), "between items there is nothing", names(1), "")
    Check.eq_str(~Report.new(), "a parameter", look(8, "x"), "2:10 param | +x: Shape")
    Check.eq_str(~Report.new(), "a template parameter's arrow type", look(8, "f"), "2:31 param | ~f: U32 -> U32")
    Check.eq_str(~Report.new(), "a case binder", look(8, "r"), "4:17 local | case Circle{+r}:")
    Check.eq_str(~Report.new(), "a destructured let", look(8, "b"), "6:12 local | (a, K{b}) = pair(y)")
    Check.eq_str(~Report.new(), "a do-bind", look(16, "name"), "14:4 local | name : String <- IO.get_env(\"USER\")")
    Check.eq_str(~Report.new(), "a later parameter with type arguments", look(25, "second"), "23:14 param | second: List<&2, U32>")
    Check.eq_str(~Report.new(), "not a local", look(8, "pair"), "-")
    Check.eq_str(~Report.new(), "out of scope", look(10, "r"), "-")

#|ok deep in a case
#|ok a lambda's binder on its own line
#|ok the next case sees none of the first
#|ok do-binds and typed lets
#|ok a law's for
#|ok a header over three lines
#|ok between items there is nothing
#|ok a parameter
#|ok a template parameter's arrow type
#|ok a case binder
#|ok a destructured let
#|ok a do-bind
#|ok a later parameter with type arguments
#|ok not a local
#|ok out of scope
