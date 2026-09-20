# rule fuel: a call to a def of the same file passes a Nat literal (`1000n`)
# where that def takes its fuel (a parameter named `fuel`, `gas`, `steps` or
# `budget`, or starting with `fuel`). The fuel-0 arm returns what it has, so
# input past the literal comes out cut short, with no error (a JSON printer
# that stopped at 1000 tasks). Inside a law, the checker unrolls the fixed
# fuel and hangs. Derive the fuel from the input's size (`Nat.mul(size, 4n)`)
# or take it as a parameter. A def's own calls are exempt: its step passes
# `fuel - 1`, not a literal.
import Base
import ../../src.bend as Src
import ../../../lazy/lazy.bend as Lazy
import ../../finding.bend as F
import ../../../syntax/lex.bend as Lex
import ../../../syntax/tree.bend as Tree
import ../../../syntax/bind.bend as Bind

# a def of the file and the position of a fuel parameter
type Fuel is Data:
  Fuel{name: String, at: Nat}

# is it a fuel parameter's name?
def is_fuel(+n: String) -> Bool:
  Bool.or(String.starts_with(n, "fuel"),
    List.contains(~String, ~String.eq, ["gas", "steps", "budget"], n))

# the arguments of a group, split at its top-level commas (each a chain)
def args.go(kids: Tree.Node, cur: Tree.Node, acc: List<&2, Tree.Node>) -> List<&2, Tree.Node>:
  match kids:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TComma{}, t, l, c}}, rest}:
      args.go(rest, Tree.NNil{}, Tree.reverse(cur, Tree.NNil{}) <> acc)
    case Tree.NCons{h, rest}:
      args.go(rest, Tree.NCons{h, cur}, acc)
    case other:
      List.reverse(&2, Tree.Node, Tree.reverse(cur, Tree.NNil{}) <> acc)

# the arguments of a group
def args(kids: Tree.Node) -> List<&2, Tree.Node>:
  args.go(kids, Tree.NNil{}, [])

# the first plain name of a parameter (`fuel` of `+fuel: Nat`)
def param(n: Tree.Node) -> String:
  match n:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, t, l, c}}, rest}:
      t
    case Tree.NCons{h, rest}:
      param(rest)
    case other:
      ""

# the fuel parameters among a def's parameters, from position i on
def fuels.params(ps: List<&2, Tree.Node>, +name: String, +i: Nat) -> List<&2, Fuel>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{p, rest}:
      +more = fuels.params(rest, name, 1n+i)
      Bool.pick(List<&2, Fuel>, is_fuel(param(p)), Fuel{name, i} <> more, more)

# the parameter group of a def's header: its first `(..)`
def header(kids: Tree.Node) -> List<&2, Tree.Node>:
  match kids:
    case Tree.NCons{Tree.Group{Lex.Tok{k, +o, l, c}, gk, close}, rest}:
      Lazy.stop(List<&2, Tree.Node>, String.eq(o, "("), args(gk), _u => header(rest))
    case Tree.NCons{h, rest}:
      header(rest)
    case other:
      Nil{}

# the fuel parameters of a def, when it has a name
def fuels.def(m: Maybe<&2, String>, kids: Tree.Node) -> List<&2, Fuel>:
  match m:
    case None{}:
      Nil{}
    case Some{name}:
      fuels.params(header(kids), name, 0n)

# every fuel parameter of every def of the file
def fuels(root: Tree.Node) -> List<&2, Fuel>:
  match root:
    case Tree.NCons{Tree.Stmt{Tree.SDef{}, +kids, body}, rest}:
      List.append(&2, Fuel, fuels.def(Bind.declared(kids), kids), fuels(rest))
    case Tree.NCons{h, rest}:
      fuels(rest)
    case other:
      Nil{}

# the nth argument, or nothing
def arg(as: List<&2, Tree.Node>, n: Nat) -> Tree.Node:
  match as n:
    case Con{h, t} 0n:
      h
    case Con{h, t} 1n+p:
      arg(t, p)
    case Nil{} m:
      Tree.NNil{}

# an argument that is a Nat literal alone, as a finding
def literal(a: Tree.Node, +path: String) -> List<&2, F.Finding>:
  match a:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TNum{}, +t, l, c}}, Tree.NNil{}}:
      Bool.pick(List<&2, F.Finding>, String.ends_with(t, "n"),
        [F.Finding{path, l, c, U32.from_nat(String.length(t)), "fuel",
          "a fixed fuel of " ++ t ++ ": input past it is cut short silently; derive the fuel from the input's size"}],
        [])
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
        _u => List.append(&2, F.Finding, literal(arg(as, at), path), more))

# every call at any depth of a chain, but the def's own (self)
def calls(n: Tree.Node, +fs: List<&2, Fuel>, +self: String, +path: String) -> List<&2, F.Finding>:
  match n:
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, +t, l, c}}, Tree.NCons{Tree.Group{open, +kids, close}, rest}}:
      +more = List.concat(&2, F.Finding, [calls(kids, fs, self, path), calls(rest, fs, self, path)])
      Lazy.stop(List<&2, F.Finding>, Bool.not(Bool.and(Lex.is_name(k), Bool.not(String.eq(t, self)))), more,
        _u => List.append(&2, F.Finding, call(fs, t, args(kids), path), more))
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
def own(m: Maybe<&2, String>) -> String:
  match m:
    case None{}:
      ""
    case Some{n}:
      n

# each top-level statement, walked as its own def
def check.go(root: Tree.Node, +fs: List<&2, Fuel>, +path: String) -> List<&2, F.Finding>:
  match root:
    case Tree.NCons{Tree.Stmt{kind, +kids, body}, rest}:
      +self = own(Bind.declared(kids))
      List.concat(&2, F.Finding, [calls(kids, fs, self, path), calls(body, fs, self, path), check.go(rest, fs, path)])
    case Tree.NCons{h, rest}:
      check.go(rest, fs, path)
    case other:
      Nil{}

# the rule
def check(s: Src.Src) -> List<&2, F.Finding>:
  Src.Src{path, text, toks, +tree, bound, items} = s
  check.go(tree, fuels(tree), path)
