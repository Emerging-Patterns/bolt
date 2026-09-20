# rule shadow: a let, a do-bind, a lambda or a pattern binds a name that a
# def above it in the same file already has. When the file is imported, Bend
# reads such a name as a reference to the def, and the binder fails with an
# error that points at the pattern: "a pattern (a binder or a constructor)".
# Parameters and `for` names are declared, not parsed as terms, and are safe.
import Base
import ../../src.bend as Src
import ../../../lazy/lazy.bend as Lazy
import ../../finding.bend as F
import ../../../syntax/bind.bend as Bind

# is the binder parsed as a term (where a def's name wins)?
def binds_as_term(k: Bind.BindKind) -> Bool:
  match k:
    case Bind.KLocal{}:
      True{}
    case Bind.KPat{}:
      True{}
    case other:
      False{}

# the defs of the file declared above a line, by name
def declared_above(binds: List<&2, Bind.Bind>, +name: String, +line: U32) -> Bool:
  match binds:
    case Nil{}:
      False{}
    case Con{Bind.Bind{+n, +l, c, Bind.KItem{}, note}, rest}:
      Lazy.or_else(Bool.and(String.eq(n, name), U32.is_lt(l, line)), _u => declared_above(rest, name, line))
    case Con{other, rest}:
      declared_above(rest, name, line)

def check.go(binds: List<&2, Bind.Bind>, +all: List<&2, Bind.Bind>, +path: String) -> List<&2, F.Finding>:
  match binds:
    case Nil{}:
      Nil{}
    case Con{Bind.Bind{+name, +line, +col, kind, note}, rest}:
      +more = check.go(rest, all, path)
      Bool.pick(List<&2, F.Finding>,
        Bool.and(binds_as_term(kind), declared_above(all, name, line)),
        F.Finding{path, line, col, U32.from_nat(String.length(name)), "shadow",
          name ++ " is a def above; imported, this binder would read as it"} <> more,
        more)

def check.on(b: Bind.Bound, path: String) -> List<&2, F.Finding>:
  Bind.Bound{+binds, uses, scopes} = b
  check.go(binds, binds, path)

# the rule
def check(s: Src.Src) -> List<&2, F.Finding>:
  Src.Src{path, text, toks, tree, bound, items} = s
  check.on(bound, path)
