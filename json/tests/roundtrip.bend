# json: parse then print, over every kind of value
import Base
import ../parse.bend as Parse
import ../print.bend as Print
import ../../wire/check/kit.bend as Check
import ../../wire/check/print.bend as Report

# parses and prints back; a parse failure prints as "<bad>"
def again(text: String) -> String:
  Print.maybe(Parse.parse(text))

def main() -> IO(Unit):
  do IO<Unit>:
    Check.eq_str(~Report.new(), "null", again("null"), "null")
    Check.eq_str(~Report.new(), "booleans", again("[true,false]"), "[true,false]")
    Check.eq_str(~Report.new(), "numbers keep their text", again("[0,-12,3.50,1e9]"), "[0,-12,3.50,1e9]")
    Check.eq_str(~Report.new(), "whitespace goes", again(" { \"a\" : [ 1 , 2 ] ,\n\t\"b\" : { } } "), "{\"a\":[1,2],\"b\":{}}")
    Check.eq_str(~Report.new(), "escapes", again("\"q\\\" b\\\\ n\\n t\\t u\\u0041\""), "\"q\\\" b\\\\ n\\n t\\t uA\"")
    Check.eq_str(~Report.new(), "nesting", again("[[[]],{\"k\":{\"k\":[null]}}]"), "[[[]],{\"k\":{\"k\":[null]}}]")
    Check.eq_str(~Report.new(), "empty input is bad", again(""), "<bad>")
    Check.eq_str(~Report.new(), "unclosed array is bad", again("[1,2"), "<bad>")
    Check.eq_str(~Report.new(), "stray close is bad", again("]"), "<bad>")
    Check.eq_str(~Report.new(), "two roots are bad", again("1 2"), "<bad>")
    Check.eq_str(~Report.new(), "unclosed string is bad", again("\"abc"), "<bad>")
    Check.eq_str(~Report.new(), "mismatched close is bad", again("[}"), "<bad>")

#|ok null
#|ok booleans
#|ok numbers keep their text
#|ok whitespace goes
#|ok escapes
#|ok nesting
#|ok empty input is bad
#|ok unclosed array is bad
#|ok stray close is bad
#|ok two roots are bad
#|ok unclosed string is bad
#|ok mismatched close is bad
