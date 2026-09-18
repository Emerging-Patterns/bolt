# json/print: a value to compact text.
import Base
import ./value.bend as V

def escape.char(c: Char) -> String:
  match c:
    case '"':
      "\\\""
    case '\\':
      "\\\\"
    case '\n':
      "\\n"
    case '\r':
      "\\r"
    case '\t':
      "\\t"
    case other:
      String.from_list([other])

# the chars of a string with `"`, `\\` and control chars escaped
def escape(cs: List<&2, Char>) -> String:
  match cs:
    case Nil{}:
      ""
    case Con{c, t}:
      escape.char(c) ++ escape(t)

# a string in quotes, escaped
def quote(s: String) -> String:
  "\"" ++ escape(String.to_list(s)) ++ "\""

# a value as compact JSON
def print(j: V.Json) -> String:
  match j:
    case V.JNull{}:
      "null"
    case V.JBool{True{}}:
      "true"
    case V.JBool{False{}}:
      "false"
    case V.JNum{raw}:
      raw
    case V.JStr{s}:
      quote(s)
    case V.JArr{items}:
      "[" ++ print(items) ++ "]"
    case V.JObj{pairs}:
      "{" ++ print(pairs) ++ "}"
    case V.JNil{}:
      ""
    case V.JCons{h, V.JNil{}}:
      print(h)
    case V.JCons{h, t}:
      print(h) ++ "," ++ print(t)
    case V.JPair{k, v, V.JNil{}}:
      quote(k) ++ ":" ++ print(v)
    case V.JPair{k, v, r}:
      quote(k) ++ ":" ++ print(v) ++ "," ++ print(r)

# a parse result: the value, or "<bad>"
def maybe(m: Maybe<&2, V.Json>) -> String:
  match m:
    case None{}:
      "<bad>"
    case Some{j}:
      print(j)
