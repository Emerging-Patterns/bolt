# json: building values and reading them back by path
import Base
import ../value.bend as V
import ../parse.bend as Parse
import ../print.bend as Print
import ../../core/check/kit.bend as Check
import ../../core/check/print.bend as Report

def msg() -> V.Json:
  V.obj([("id", V.num(7)), ("method", V.JStr{"open"}),
    ("params", V.obj([("uri", V.JStr{"file:///a.bend"}), ("tags", V.arr([V.JNull{}, V.JBool{True{}}]))]))])

def parsed(m: Maybe<&2, V.Json>) -> V.Json:
  Maybe.default(&2, V.Json, m, V.JNull{})

def main() -> IO(Unit):
  do IO<Unit>:
    Check.eq_str(~Report.new(), "a built value prints", Print.print(msg()),
      "{\"id\":7,\"method\":\"open\",\"params\":{\"uri\":\"file:///a.bend\",\"tags\":[null,true]}}")
    Check.eq_str(~Report.new(), "a path reads a string", V.str_or(V.get(V.get(msg(), "params"), "uri"), "?"), "file:///a.bend")
    Check.eq_u32(~Report.new(), "a number reads", V.u32_or(V.get(msg(), "id"), 0), 7)
    Check.eq_str(~Report.new(), "a missing key reads the default", V.str_or(V.get(V.get(msg(), "nope"), "uri"), "?"), "?")
    Check.eq_u32(~Report.new(), "a string is not a number", V.u32_or(V.get(msg(), "method"), 99), 99)
    Check.eq_str(~Report.new(), "parsed text reads the same", V.str_or(V.get(parsed(Parse.parse("{\"a\":{\"b\":\"deep\"}}")), "a"), "?"), "?")
    Check.eq_str(~Report.new(), "parsed paths chain", V.str_or(V.get(V.get(parsed(Parse.parse("{\"a\":{\"b\":\"deep\"}}")), "a"), "b"), "?"), "deep")

#|ok a built value prints
#|ok a path reads a string
#|ok a number reads
#|ok a missing key reads the default
#|ok a string is not a number
#|ok parsed text reads the same
#|ok parsed paths chain
