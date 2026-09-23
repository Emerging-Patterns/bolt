# rule param: a parameter name shorter than 2 characters. A single uppercase
# letter is a type parameter (`A`, `T`), and a bare parameter or one typed
# `Quant` is a quantity. Locals, pattern binders and a law's `for` names are
# not parameters. A PROOF.bend's parameters are the names the law bound.
import Base
import ../../paths.bend as Paths
import ../../src.bend as Src
import ../../finding.bend as F
import ../../../syntax/bind.bend as Bind
import ../../../lazy/lazy.bend as Lazy

# one character, and a capital: a type parameter
def check.letter(cs: List<&2, Char>) -> Bool:
  match cs:
    case Con{c, Nil{}}:
      Char.is_upper(c)
    case other:
      False{}

# `A`, `T`, `H`
def check.upper(+nm: String) -> Bool:
  check.letter(String.to_list(nm))

# no type, or `: Quant`: a quantity parameter (`a` in `List<a, A>`)
def check.quant(+note: String) -> Bool:
  Bool.or(Bool.not(String.contains(note, ":")), String.ends_with(note, ": Quant"))

# shorter than 2
def check.short(+nm: String) -> Bool:
  Nat.is_lt(String.length(nm), 2n)

# a parameter, not a local or a pattern
def check.is_param(kk: Bind.BindKind) -> Bool:
  match kk:
    case Bind.KParam{}:
      True{}
    case other:
      False{}

# a type parameter or a quantity, which are allowed to be one letter
def check.allowed(+nm: String, +note: String) -> Bool:
  Bool.or(check.upper(nm), check.quant(note))

def check.go(binds: List<&2, Bind.Bind>, +path: String) -> List<&2, F.Finding>:
  match binds:
    case Nil{}:
      Nil{}
    case Con{Bind.Bind{+nm, +line, +col, +kind, +note}, rest}:
      +more = check.go(rest, path)
      +hit = Bool.and(check.is_param(kind), Bool.and(check.short(nm), Bool.not(check.allowed(nm, note))))
      Bool.pick(List<&2, F.Finding>, hit,
        F.Finding{path, line, col, U32.from_nat(String.length(nm)), "param",
          "Parameter " ++ nm ++ " is shorter than 2 characters."} <> more, more)

def check.on(binds: List<&2, Bind.Bind>, +path: String) -> List<&2, F.Finding>:
  Lazy.stop(List<&2, F.Finding>, Paths.is_proof(path), [], _u => check.go(binds, path))

# the rule; a proof's parameters stay the law's names
def check(ss: Src.Src) -> List<&2, F.Finding>:
  Src.Src{path, text, toks, tree, bound, items} = ss
  Bind.Bound{binds, uses, scopes} = bound
  check.on(binds, path)
