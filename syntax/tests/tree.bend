# syntax/tree: statements, groups, and recovery from broken brackets
import Base
import ../tree.bend as Tree
import ../lex.bend as Lex
import ../../wire/check/kit.bend as Check
import ../../wire/check/print.bend as Report

def show(src: String) -> String:
  Tree.show(Tree.parse(src))

def source() -> String:
  String.join([
    "# doc",
    "def f(+x: List<&2, U32>, y: U32) -> U32:",
    "  match x:",
    "    case Con{h, t}:",
    "      z = (h + y : U32)  # sum",
    "      z",
    "    case Nil{}:",
    "      0",
    "",
    "type T<A> is Data:",
    "  K{a: A}"], "\n")

def sig(src: String) -> String:
  Lex.text(Tree.leaves(Tree.parse(src)))

def main() -> IO(Unit):
  do IO<Unit>:
    Check.eq_str(~Report.new(), "statements nest by indent, groups by brackets", show(source()),
      "[def f (+ x : List <&2 , U32> , y : U32) -> U32 : {[match x : {[case Con {h , t} : {[z = (h + y : U32)] [z]}] [case Nil {} : {[0]}]}]}] [type T <A> is Data : {[K {a : A}]}]")
    Check.eq_str(~Report.new(), "a call over lines is one statement", show("f(a,\n  b)\nc"), "[f (a , b)] [c]")
    Check.eq_str(~Report.new(), "a header over lines, then its body", show("def g(\n  a: U32\n) -> U32:\n  a"),
      "[def g (a : U32) -> U32 : {[a]}]")
    Check.eq_str(~Report.new(), ">> closes two angle groups", show("x: List<List<U32>>"), "[x : List <List <U32>>]")
    Check.eq_str(~Report.new(), "less-than is not a bracket", show("a < b"), "[a < b]")
    Check.eq_str(~Report.new(), "<> and <- are operators", show("a <> b <- c"), "[a <> b <- c]")
    Check.eq_str(~Report.new(), "the next item closes an unclosed bracket", show("def f(x\ndef g() -> U32:\n  1"),
      "[def f (x..] [def g () -> U32 : {[1]}]")
    Check.eq_str(~Report.new(), "a stray close is a leaf", show("f(x))"), "[f (x) )]")
    Check.eq_str(~Report.new(), "a mismatched close reaches its match", show("f([x)\ny"), "[f ([x..)] [y]")
    Check.eq_str(~Report.new(), "the end of the file closes everything", show("f(x\n  y"), "[f (x y..]")
    Check.eq_str(~Report.new(), "the leaves are the significant tokens", sig("def f(x):\n  g(x)  # c"), "deff(x):g(x)")
    Check.eq_str(~Report.new(), "an empty source", show(""), "")

#|ok statements nest by indent, groups by brackets
#|ok a call over lines is one statement
#|ok a header over lines, then its body
#|ok >> closes two angle groups
#|ok less-than is not a bracket
#|ok <> and <- are operators
#|ok the next item closes an unclosed bracket
#|ok a stray close is a leaf
#|ok a mismatched close reaches its match
#|ok the end of the file closes everything
#|ok the leaves are the significant tokens
#|ok an empty source
