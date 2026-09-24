# rule put: a call to `Map.put(`: among the significant tokens, a `Map.put`
# token with a `(` token right after it. Base's Map.put is an internal helper
# of Map.set: on a leaf it keeps the old key and replaces the value without
# comparing keys, so putting a new key silently overwrites another entry
# (bend-http c91bdf8: "b" into a map of "a" replaced "a"). Use Map.set. A
# file that defines Map.put itself (Base's source), a `def` keyword with a
# `Map.put` token right after it, is exempt.
import Base
import ../../src.bend as Src
import ../../lazy/lazy.bend as Lazy
import ../../finding.bend as F
import ../../syntax/lex.bend as Lex
import ../tokens.bend as T

# is the first token `Map.put`?
def defines.named(toks: List<&2, Lex.Tok>) -> Bool:
  match toks:
    case Con{Lex.Tok{k, +t, l, c}, rest}:
      String.eq(t, "Map.put")
    case Nil{}:
      False{}

# a keyword? a token's kind is read here, its text in the tests beside it
def defines.key(kk: Lex.TokKind) -> Bool:
  match kk:
    case Lex.TKey{}:
      True{}
    case other:
      False{}

# a dotted name?
def calls.dotted(kk: Lex.TokKind) -> Bool:
  match kk:
    case Lex.TDotted{}:
      True{}
    case other:
      False{}

# does the file define Map.put: a `def` keyword right before a `Map.put`?
def defines(toks: List<&2, Lex.Tok>) -> Bool:
  match toks:
    case Con{Lex.Tok{k, +d, l, c}, +rest}:
      Lazy.or_else(Bool.and(defines.key(k), Bool.and(String.eq(d, "def"), defines.named(rest))), _u => defines(rest))
    case Nil{}:
      False{}

# a dotted name then an open bracket: a finding when they are `Map.put` and
# `(`, before what the rest reports
def calls.one(
  +tt: String,
  +oo: String,
  +ll: U32,
  +cc: U32,
  +path: String,
  +more: List<&2, F.Finding>
) -> List<&2, F.Finding>:
  Bool.pick(List<&2, F.Finding>, Bool.and(String.eq(tt, "Map.put"), String.eq(oo, "(")),
    F.Finding{path, ll, cc, 7, "put", "Map.put does not compare keys, so a new key can overwrite an existing entry; use Map.set."}
      <> more,
    more)

# every `Map.put(` among the significant tokens
def calls(toks: List<&2, Lex.Tok>, +path: String) -> List<&2, F.Finding>:
  match toks:
    case Con{Lex.Tok{k, +t, +l, +c}, +rest}:
      match rest:
        case Con{Lex.Tok{k2, +o, l2, c2}, r2}:
          Lazy.either(List<&2, F.Finding>, Bool.and(calls.dotted(k), Lex.is_open(k2)), _u => calls.one(t, o, l, c, path,
            calls(r2, path)), _v => calls(rest, path))
        case Nil{}:
          Nil{}
    case Nil{}:
      Nil{}

def check.on(+toks: List<&2, Lex.Tok>, path: String) -> List<&2, F.Finding>:
  Lazy.stop(List<&2, F.Finding>, defines(toks), [], _u => calls(toks, path))

# the rule
def check(ss: Src.Src) -> List<&2, F.Finding>:
  Src.Src{path, text, toks, tree, bound, items} = ss
  check.on(T.sig(toks), path)
