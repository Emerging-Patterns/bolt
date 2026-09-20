# rule put: a call to `Map.put(`. Base's Map.put is an internal helper of
# Map.set: on a leaf it keeps the old key and replaces the value without
# comparing keys, so putting a new key silently overwrites another entry
# (bend-http c91bdf8: "b" into a map of "a" replaced "a"). Use Map.set. A
# file that defines Map.put itself (Base's source) is exempt.
import Base
import ../../src.bend as Src
import ../../../lazy/lazy.bend as Lazy
import ../../finding.bend as F
import ../../../syntax/lex.bend as Lex
import ../tokens.bend as T

# does the file define Map.put?
def defines(toks: List<&2, Lex.Tok>) -> Bool:
  match toks:
    case Con{Lex.Tok{Lex.TKey{}, +d, l, c}, Con{Lex.Tok{k, +t, l2, c2}, rest}}:
      Lazy.or_else(Bool.and(String.eq(d, "def"), String.eq(t, "Map.put")), _u => defines(rest))
    case Con{h, rest}:
      defines(rest)
    case Nil{}:
      False{}

# every `Map.put(` among the significant tokens
def calls(toks: List<&2, Lex.Tok>, +path: String) -> List<&2, F.Finding>:
  match toks:
    case Con{Lex.Tok{Lex.TDotted{}, +t, l, c}, Con{Lex.Tok{Lex.TOpen{}, +o, l2, c2}, rest}}:
      +more = calls(rest, path)
      Bool.pick(List<&2, F.Finding>, Bool.and(String.eq(t, "Map.put"), String.eq(o, "(")),
        F.Finding{path, l, c, 7, "put", "Map.put never compares keys; a new key overwrites another entry: use Map.set"}
          <> more,
        more)
    case Con{h, rest}:
      calls(rest, path)
    case Nil{}:
      Nil{}

def check.on(+toks: List<&2, Lex.Tok>, path: String) -> List<&2, F.Finding>:
  Bool.pick(List<&2, F.Finding>, defines(toks), [], calls(toks, path))

# the rule
def check(s: Src.Src) -> List<&2, F.Finding>:
  Src.Src{path, text, toks, tree, bound, items} = s
  check.on(T.sig(toks), path)
