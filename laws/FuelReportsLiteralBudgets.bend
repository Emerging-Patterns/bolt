# `fuel` reports exactly an argument that is one Nat literal token alone, or
# the dotted name `U32.to_nat` then a `(` group holding one U32 literal token
# (digits) alone, in a call (not a self-call) to a def of the file that
# returns no effect (its header, wrapped over lines or not, holds no
# top-level `->` token followed right away by the capitalized name token
# `IO`), at a parameter named
# `fuel`, `gas`, `steps` or `budget` or starting with `fuel`.
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/syntax/bind.bend as Bind
import ../src/src.bend as Src
import ../src/syntax/tree.bend as Tree
import ../src/syntax/outline.bend as Outline
import ../src/rules/calls.bend as Calls
import ../src/rules/tokens.bend as T
import ../src/rules/pedantic/fuel.bend as FuelRule

# fuel (laws/FuelReportsLiteralBudgets.bend). The rule lists the file's fuel parameters: for each
# def of the file (Calls.defs) that returns no effect, each parameter
# (Calls.params) whose name, its first lowercase name before the colon
# (Calls.param_name), is `fuel`, `gas`, `steps` or `budget` or starts with
# `fuel`, with its position. A def returns an effect when its header's
# top-level tokens (the whole header: laws/DefSignatureRunsToItsColon.bend)
# hold a `->` leaf followed right away by a capitalized name leaf `IO`. Over
# each top-level statement it then reads every call at any depth, a name
# token then a `(` group, that is not a call of the statement's own name (a
# self-call): for each fuel parameter of a def of that name, one finding when
# the argument in its position (Calls.args, split at top-level commas) is one
# Nat literal token alone, digits then `n`, or the dotted name `U32.to_nat`
# then a `(` group holding one U32 literal token alone, digits only.

# is the name a fuel parameter's: `fuel`, `gas`, `steps` or `budget`, or one
# starting with `fuel`?
def fuel.named(+nn: String) -> Bool:
  Bool.or(String.starts_with(nn, "fuel"), List.contains(~String, ~String.eq, ["gas", "steps",
    "budget"], nn))

# the parameters with a fuel name among ps, the first at position i, each
# with the def's name
def fuel.slots.of(ps: List<&2, Tree.Node>, +name: String, +ii: Nat) -> List<&2, FuelRule.Fuel>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{p, rest}:
      +more = fuel.slots.of(rest, name, 1n+ii)
      Bool.pick(List<&2, FuelRule.Fuel>, fuel.named(Calls.param_name(p)), FuelRule.Fuel{name, ii} <> more, more)

# is the node after an arrow a capitalized name leaf reading `IO`?
def fuel.io.next(nn: Tree.Node) -> Bool:
  match nn:
    case Tree.NCons{+g, rest}:
      Bool.and(Calls.kind.leaf(~Calls.kind.upper, g), String.eq(Calls.leaf.text(g), "IO"))
    case other:
      False{}

# does the header return an effect: some top-level `->` leaf followed right
# away by a capitalized name leaf reading `IO`?
def fuel.io(sig: Tree.Node) -> Bool:
  match sig:
    case Tree.NCons{h, +rest}:
      Bool.or(Bool.and(Calls.kind.leaf(~Calls.kind.arrow, h), fuel.io.next(rest)), fuel.io(rest))
    case other:
      False{}

# the parameters of a def that returns no effect, none of one that does
def fuel.params(+sig: Tree.Node) -> List<&2, Tree.Node>:
  Bool.pick(List<&2, Tree.Node>, fuel.io(sig), [], Calls.params(sig))

# every fuel parameter of every def that returns no effect, in order
def fuel.slots(ds: List<&2, Calls.Def>) -> List<&2, FuelRule.Fuel>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{Calls.Def{name, sig, body}, rest}:
      List.append(&2, FuelRule.Fuel, fuel.slots.of(fuel.params(sig), name, 0n), fuel.slots(rest))

# does a call's group hold one number token alone, digits only (a U32
# literal), when ok says the call is `U32.to_nat(`?
def fuel.conv(kids: Tree.Node, ok: Bool) -> Bool:
  match kids:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TNum{}, +t, l, c}}, Tree.NNil{}}:
      Bool.and(ok, T.digits_ok(String.to_list(t)))
    case other:
      False{}

# is the argument one Nat literal token alone, digits then `n`, or the
# dotted name `U32.to_nat` then a `(` group holding one U32 literal alone?
def fuel.lone(aa: Tree.Node) -> Bool:
  match aa:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TNum{}, +t, l, c}}, Tree.NNil{}}:
      T.nat_ok(String.to_list(t))
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TDotted{}, +t, l, c}},
      Tree.NCons{Tree.Group{Lex.Tok{ok, +o, ol, oc}, kids, cl}, Tree.NNil{}}}:
      fuel.conv(kids, Bool.and(String.eq(t, "U32.to_nat"), String.eq(o, "(")))
    case other:
      False{}

# how many fuel parameters of defs named name a call with these arguments
# fills with a fixed number (fuel.lone)
def fuel.hits(fs: List<&2, FuelRule.Fuel>, +name: String, +as: List<&2, Tree.Node>) -> Nat:
  match fs:
    case Nil{}:
      0n
    case Con{FuelRule.Fuel{+fn, at}, rest}:
      +m = fuel.hits(rest, name, as)
      Bool.pick(Nat, Bool.and(String.eq(fn, name), fuel.lone(Calls.arg(as, at))), 1n+m, m)

# how many fixed numbers the calls under the node pass for fuel, at any
# depth: a call is a name token then a `(` group, and a call of self is not
# counted
def fuel.count(nn: Tree.Node, +fs: List<&2, FuelRule.Fuel>, +self: String) -> Nat:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, +t, l, c}}, Tree.NCons{Tree.Group{Lex.Tok{ok, +o, ol, oc}, +kids, close},
      rest}}:
      +m = Nat.add(fuel.count(kids, fs, self), fuel.count(rest, fs, self))
      Bool.pick(Nat, Bool.and(Bool.and(Lex.is_name(k), String.eq(o, "(")), Bool.not(String.eq(t, self))),
        Nat.add(fuel.hits(fs, t, Calls.args(kids)), m), m)
    case Tree.NCons{Tree.Group{open, kids, close}, rest}:
      Nat.add(fuel.count(kids, fs, self), fuel.count(rest, fs, self))
    case Tree.NCons{Tree.Stmt{kind, kids, body}, rest}:
      Nat.add(fuel.count(kids, fs, self), Nat.add(fuel.count(body, fs, self), fuel.count(rest, fs, self)))
    case Tree.NCons{h, rest}:
      fuel.count(rest, fs, self)
    case other:
      0n

# a statement's own name, "" when it has none
def fuel.own(mm: Maybe<&2, String>) -> String:
  match mm:
    case None{}:
      ""
    case Some{nm}:
      nm

# the fuel literals of the file: each top-level statement's calls, its own
# name the self it does not count
def fuel.total(root: Tree.Node, +fs: List<&2, FuelRule.Fuel>) -> Nat:
  match root:
    case Tree.NCons{Tree.Stmt{kind, +kids, body}, rest}:
      +self = fuel.own(Bind.declared(kids))
      Nat.add(fuel.count(kids, fs, self), Nat.add(fuel.count(body, fs, self), fuel.total(rest, fs)))
    case Tree.NCons{h, rest}:
      fuel.total(rest, fs)
    case other:
      0n

# LAW: the rule's fuel parameters are the parameters with a fuel name of the
# file's defs that return no effect (no `-> IO`), each at its position
law fuel_slots:
  for ds: List<&2, Calls.Def>
  {FuelRule.fuels(ds) == fuel.slots(ds) : List<&2, FuelRule.Fuel>}

# LAW: over any chain, fuel reports one finding for each fuel parameter a
# call (not of self) fills with a lone Nat literal or `U32.to_nat` of a lone
# U32 literal, and none for anything else
law fuel_walk_counts:
  for nn: Tree.Node
  for +fs: List<&2, FuelRule.Fuel>
  for +self: String
  for +path: String
  {List.length(&2, F.Finding, FuelRule.calls(nn, fs, self, path)) == fuel.count(nn, fs, self) : Nat}

# LAW: fuel reports exactly those literals over the file's top-level
# statements, against the fuel parameters of the file's defs
law fuel_counts:
  for path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for +tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, FuelRule.check(Src.Src{path, text, toks, tree, bound, items}))
    == fuel.total(tree, fuel.slots(Calls.defs(tree))) : Nat}
