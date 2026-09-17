# lsp/report: the checker's text, as diagnostics. The fixtures are bend 2.0.3's
# own output: when a bend update changes the format, this test says so.
import Base
import ../report.bend as Rep
import ../../wire/check/kit.bend as Check
import ../../wire/check/print.bend as Report

def show.go(ds: List<&2, Rep.Diag>) -> String:
  match ds:
    case Nil{}:
      ""
    case Con{Rep.Diag{line, msg}, t}:
      "[" ++ U32.show(line) ++ "|" ++ msg ++ "]" ++ show.go(t)

def show(text: String) -> String:
  show.go(Rep.parse(text))

def type_error() -> String:
  "Error:\n- expected : String\n- observed : U32\nContext:\n- x : U32\nLocation: f\n3 | def f(x: U32) -> String:\n4>|   x\n5 | \n"

def syntax_error() -> String:
  "Error:\n- expected : a name\n- observed : ':'\nLocation:\n2 | \n3>| def f(x: U32 -> U32:\n4 |   x\n"

def arrow_line() -> String:
  "Error:\n- message  : bad\nLocation: g\n 9 | def g() -> U32:\n10>|   (x => x)(y > 2)\n11 | \n"

def elsewhere() -> String:
  "Error:\n- expected : c\n- observed : c (consumed more than once)\nLocation: ../lex.feed\n133 | \n134>| def feed(c: Char, st: Lex) -> Lex:\n135 |   Lex{mode, buf, toks} = st\n"

def todo() -> String:
  "Error: 1 TODO found.\nThe code is incomplete, and not a valid proof yet.\n"

def twice() -> String:
  "Error:\n- message  : one\nLocation: a\n1>| x\nError:\n- message  : two\nLocation: b\n7>| y\n"

def main() -> IO(Unit):
  do IO<Unit>:
    Check.eq_str(~Report.new(), "clean output has no diagnostics", show("All terms check.\n"), "")
    Check.eq_str(~Report.new(), "a module with no main is clean", show("Error: no main to run\n"), "")
    Check.eq_str(~Report.new(), "a type error lands on its marked line, 0-based", show(type_error()),
      "[3|expected : String\nobserved : U32\nContext:\nx : U32]")
    Check.eq_str(~Report.new(), "a syntax error has no def name", show(syntax_error()), "[2|expected : a name\nobserved : ':']")
    Check.eq_str(~Report.new(), "a > in the source line does not hide the marker", show(arrow_line()), "[9|message  : bad]")
    Check.eq_str(~Report.new(), "an error in an import lands on line 0, named", show(elsewhere()),
      "[0|in ../lex.feed:\nexpected : c\nobserved : c (consumed more than once)]")
    Check.eq_str(~Report.new(), "an open goal count has no location", show(todo()),
      "[0|1 TODO found.\nThe code is incomplete, and not a valid proof yet.]")
    Check.eq_str(~Report.new(), "two errors are two diagnostics", show(twice()), "[0|message  : one][6|message  : two]")

#|ok clean output has no diagnostics
#|ok a module with no main is clean
#|ok a type error lands on its marked line, 0-based
#|ok a syntax error has no def name
#|ok a > in the source line does not hide the marker
#|ok an error in an import lands on line 0, named
#|ok an open goal count has no location
#|ok two errors are two diagnostics
