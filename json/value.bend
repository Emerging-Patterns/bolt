# json/value: a JSON value. Arrays and objects hold their cells inside the
# type (JCons, JPair, JNil) rather than in a List, so every traversal is a
# structural recursion on one argument -- which Bend's termination checker
# accepts, and which keeps laws provable. Build and read them through the
# defs below, never by hand.
import Base

type Json is Data:
  JNull{}
  JBool{b: Bool}
  JNum{raw: String}
  JStr{s: String}
  JArr{items: Json}
  JObj{pairs: Json}
  JNil{}
  JCons{head: Json, tail: Json}
  JPair{key: String, val: Json, rest: Json}

# reverses a chain of JCons or JPair cells onto acc
def reverse(cells: Json, acc: Json) -> Json:
  match cells:
    case JCons{h, t}:
      reverse(t, JCons{h, acc})
    case JPair{k, v, r}:
      reverse(r, JPair{k, v, acc})
    case _:
      acc

# builders
def arr.go(items: List<&2, Json>) -> Json:
  match items:
    case Nil{}:
      JNil{}
    case Con{h, t}:
      JCons{h, arr.go(t)}

def arr(items: List<&2, Json>) -> Json:
  JArr{arr.go(items)}

def obj.go(pairs: List<&1, String & Json>) -> Json:
  match pairs:
    case Nil{}:
      JNil{}
    case Con{(k, v), t}:
      JPair{k, v, obj.go(t)}

def obj(pairs: List<&1, String & Json>) -> Json:
  JObj{obj.go(pairs)}

def num(n: U32) -> Json:
  JNum{U32.show(n)}

# accessors: a missing key or a wrong kind reads as JNull / None / the default,
# so paths chain: get(get(msg, "params"), "textDocument")
def find(cells: Json, +key: String) -> Json:
  match cells:
    case JPair{+k, v, r}:
      Bool.pick(Json, String.eq(k, key), v, find(r, key))
    case other:
      JNull{}

def get(j: Json, key: String) -> Json:
  match j:
    case JObj{pairs}:
      find(pairs, key)
    case other:
      JNull{}

def str_or(j: Json, default: String) -> String:
  match j:
    case JStr{s}:
      s
    case other:
      default

def u32_or(j: Json, default: U32) -> U32:
  match j:
    case JNum{raw}:
      Maybe.default(&2, U32, U32.read(raw), default)
    case other:
      default
