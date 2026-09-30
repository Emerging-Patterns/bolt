# rule fuel: a call to a def of the same file, its name then `(`, passes a
# fixed number where that def takes its fuel: a Nat literal (`1000n`: digits,
# then `n`), or `U32.to_nat` of a U32 literal (`U32.to_nat(100000)`: digits
# alone), the form a big fuel is written in. A fuel parameter is known by its
# name alone (its first lowercase name before the colon): `fuel`, `gas`,
# `steps` or `budget`, or any name starting with `fuel`. The fuel-0 arm
# returns what it has, so input past the number comes out cut short, with no
# error (a JSON printer that stopped at 1000 tasks). A law is no safer: a law
# proved over every fuel and then used at a big fixed one, against a goal
# written another way, overflows the checker ("the machine stack overflowed",
# bend 2.0.33 and 2.0.34; ez's lock walk at `U32.to_nat(100000)` did). Before
# 2.0.29 the checker unrolled the fixed fuel and hung; 2.0.29 made a checked
# recursion on a Nat literal linear. Derive the fuel from the input's size
# (`Nat.mul(size, 4n)`) or take it as a parameter. A number of any size
# counts, an exact repeat count such as `3n` included. Only an argument that
# is the literal alone, or `U32.to_nat(` the U32 literal alone `)`, counts: a
# let-bound literal and a parenthesized `(7n)` are not seen. A def's own calls
# are exempt: its step passes `fuel - 1`, not a literal.
import Base
import ../../src.bend as Src
import ../../lazy/lazy.bend as Lazy
import ../../finding.bend as F
import ../../syntax/lex.bend as Lex
import ../../syntax/tree.bend as Tree
import ../../syntax/bind.bend as Bind
import ../calls.bend as Calls
import ../tokens.bend as T

# a def of the file and the position of a fuel parameter
type Fuel is Data:
  Fuel{name: String, at: Nat}

# is it a fuel parameter's name?
def is_fuel(+nn: String) -> Bool:
  Bool.or(String.starts_with(nn, "fuel"),
    List.contains(~String, ~String.eq, ["gas", "steps", "budget"], nn))

# the fuel parameters among a def's parameters, from position i on
def fuels.params(ps: List<&2, Tree.Node>, +name: String, +ii: Nat) -> List<&2, Fuel>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{p, rest}:
      +more = fuels.params(rest, name, 1n+ii)
      Bool.pick(List<&2, Fuel>, is_fuel(Calls.param_name(p)), Fuel{name, ii} <> more, more)

# every fuel parameter of every def of the file
def fuels(ds: List<&2, Calls.Def>) -> List<&2, Fuel>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{Calls.Def{name, sig, body}, rest}:
      List.append(&2, Fuel, fuels.params(Calls.params(sig), name, 0n), fuels(rest))

# the group of a call at line ll, column cc, as a finding when it holds one
# U32 literal alone (digits) and ok says the call is `U32.to_nat(`
def converted(kids: Tree.Node, ok: Bool, +ll: U32, +cc: U32, +path: String) -> List<&2, F.Finding>:
  match kids:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TNum{}, +t, l, c}}, Tree.NNil{}}:
      Bool.pick(List<&2, F.Finding>, Bool.and(ok, T.digits_ok(String.to_list(t))),
        [F.Finding{path, ll, cc, U32.from_nat(Nat.add(String.length(t), 12n)), "fuel",
          "The fuel is fixed at U32.to_nat(" ++ t
            ++ "), so longer input is silently cut short; derive the fuel from the input size."}],
        [])
    case other:
      Nil{}

# an argument that is a Nat literal alone (digits, then `n`), or
# `U32.to_nat` of a U32 literal alone, as a finding
def literal(aa: Tree.Node, +path: String) -> List<&2, F.Finding>:
  match aa:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TNum{}, +t, l, c}}, Tree.NNil{}}:
      Bool.pick(List<&2, F.Finding>, T.nat_ok(String.to_list(t)),
        [F.Finding{path, l, c, U32.from_nat(String.length(t)), "fuel",
          "The fuel is fixed at " ++ t ++ ", so longer input is silently cut short; derive the fuel from the input size."}],
        [])
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TDotted{}, +t, l, c}},
      Tree.NCons{Tree.Group{Lex.Tok{ok, +o, ol, oc}, kids, cl}, Tree.NNil{}}}:
      converted(kids, Bool.and(String.eq(t, "U32.to_nat"), String.eq(o, "(")), l, c, path)
    case other:
      Nil{}

# a call to name with these arguments, against every fuel parameter
def call(fs: List<&2, Fuel>, +name: String, +as: List<&2, Tree.Node>, +path: String) -> List<&2, F.Finding>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{Fuel{+fn, at}, rest}:
      +more = call(rest, name, as, path)
      Lazy.stop(List<&2, F.Finding>, Bool.not(String.eq(fn, name)), more,
        _u => List.append(&2, F.Finding, literal(Calls.arg(as, at), path), more))

# every call at any depth of a chain, but the def's own (self)
def calls(nn: Tree.Node, +fs: List<&2, Fuel>, +self: String, +path: String) -> List<&2, F.Finding>:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, +t, l, c}}, Tree.NCons{Tree.Group{Lex.Tok{_, +o, _, _}, +kids, _}, rest}}:
      +more = List.concat(&2, F.Finding, [calls(kids, fs, self, path), calls(rest, fs, self, path)])
      +hit = Bool.and(Bool.and(Lex.is_name(k), String.eq(o, "(")), Bool.not(String.eq(t, self)))
      Lazy.stop(List<&2, F.Finding>, Bool.not(hit), more,
        _u => List.append(&2, F.Finding, call(fs, t, Calls.args(kids), path), more))
    case Tree.NCons{Tree.Group{open, kids, close}, rest}:
      List.concat(&2, F.Finding, [calls(kids, fs, self, path), calls(rest, fs, self, path)])
    case Tree.NCons{Tree.Stmt{kind, kids, body}, rest}:
      List.concat(&2, F.Finding, [calls(kids, fs, self, path), calls(body, fs, self, path),
        calls(rest, fs, self, path)])
    case Tree.NCons{h, rest}:
      calls(rest, fs, self, path)
    case other:
      Nil{}

# a def's (or a law's) name, "" when it has none
def own(mm: Maybe<&2, String>) -> String:
  match mm:
    case None{}:
      ""
    case Some{n}:
      n

# each top-level statement, walked as its own def
def check.go(root: Tree.Node, +fs: List<&2, Fuel>, +path: String) -> List<&2, F.Finding>:
  match root:
    case Tree.NCons{Tree.Stmt{kind, +kids, body}, rest}:
      +self = own(Bind.declared(kids))
      +head = calls(kids, fs, self, path)  # noqa: U013 the file's fuel defs
      +inner = calls(body, fs, self, path)  # noqa: U013 the file's fuel defs
      List.concat(&2, F.Finding, [head, inner, check.go(rest, fs, path)])
    case Tree.NCons{h, rest}:
      check.go(rest, fs, path)
    case other:
      Nil{}

# the rule
def check(ss: Src.Src) -> List<&2, F.Finding>:
  Src.Src{path, text, toks, +tree, bound, items} = ss
  check.go(tree, fuels(Calls.defs(tree)), path)
