# rule idle: a parameter a def only hands back to itself. Reported: a
# parameter of a def that calls itself, when the def's body reads its name
# and every reading of it sits in the parameter's own argument of a
# self-call: `loop(left, count)` whose one use of `count` is
# `loop(rest, Nat.add(count, 1n))`. The value goes round the recursion and
# reaches nothing: no result of the def depends on it, whatever it was
# meant to count or carry. One finding, on the parameter's name.
#
# A reading is a name leaf spelled as the parameter, or as it then a dot. A
# self-call is the def's name and then a `(` group; its arguments are the
# group's kids split at their commas, counted from 0, and the parameter's
# own argument is the one at its place among the def's parameters. A
# reading is in that argument when the nearest self-call around it holds it
# there, at any depth below (`Nat.add(count, 1n)`, a lambda's body): inside
# a self-call nested in that argument it is judged by the nested call, so
# `go(t, go(u, acc, 0))` reads acc where the inner call takes it as
# another parameter. A reading anywhere else is a use and the parameter is
# left alone: a `match` on it, an argument of another call or in another
# slot, a base arm that returns it, a pattern or a let that binds the name
# again (the spelling is what is read, so a shadowed name counts as read).
#
# Left alone as well: a parameter with no type or one written `-x` or `~x`
# (erased, a template), one whose name is not lowercase (a type) or starts
# with `_` (there to be ignored), one the signature names again (a later
# parameter's type or the return type depends on it), a def that does not
# call itself (`unused` reports a parameter nothing reads), a def that is a
# proof (it returns `-> {..}`, or has no type), and every def of a law file
# or a proof file.
#
# The fix is to delete the parameter, with its argument at each call, or to
# read it where it was meant to count: a dropped accumulator, a bound never
# compared and a counter nobody prints all have this shape, and `bend`
# accepts each of them, since passing a value on is a use to it.
import Base
import ../../src.bend as Src
import ../../finding.bend as F
import ../../syntax/lex.bend as Lex
import ../../syntax/tree.bend as Tree
import ../calls.bend as Calls
import ../../lazy/lazy.bend as Lazy

# where the walk stands against the self-calls around it: outside the
# parameter's own argument (AOut), somewhere inside it (AOwn), or among the
# arguments of a self-call, in the one at this place (AArg)
type At is Data:
  AOut{}
  AOwn{}
  AArg{place: Nat}

# is the walk in the parameter's own argument?
def own(at: At, slot: Nat) -> Bool:
  match at:
    case AOut{}:
      False{}
    case AOwn{}:
      True{}
    case AArg{place}:
      Nat.is_eq(place, slot)

# where the walk stands inside a node met here (a group, a statement): in
# the own argument or out of it, its place among the arguments forgotten
def inner(at: At, slot: Nat) -> At:
  Bool.pick(At, own(at, slot), AOwn{}, AOut{})

# among a self-call's arguments, the next one
def past.next(at: At) -> At:
  match at:
    case AArg{place}:
      AArg{1n+place}
    case other:
      other

# where the walk stands past a leaf: past a comma among a self-call's
# arguments, in the next one
def past(comma: Bool, at: At) -> At:
  match comma:
    case True{}:
      past.next(at)
    case False{}:
      at

# does a leaf read the parameter: a name spelled as it, or as it then a dot?
def reads(k: Lex.TokKind, +t: String, +nm: String) -> Bool:
  Bool.and(Lex.is_name(k), Bool.or(String.eq(t, nm), String.starts_with(t, nm ++ ".")))

# where the walk stands in a group after a leaf: at the first argument when
# they are a self-call (the def's name, then `(`), else inside
def into(o: String, t: String, name: String, at: At, slot: Nat) -> At:
  Bool.pick(At, Bool.and(String.eq(o, "("), String.eq(t, name)), AArg{0n}, inner(at, slot))

# is the parameter read anywhere but in its own argument of a self-call?
def stray(n: Tree.Node, +at: At, +slot: Nat, +nm: String, +name: String) -> Bool:
  match n:
    case Tree.NCons{Tree.Leaf{Lex.Tok{+k, +t, _l, _c}},
      Tree.NCons{Tree.Group{Lex.Tok{_ko, o, _lo, _co}, kids, _cl}, rest}}:
      +next = past(Lex.is_comma(k), at)
      +here = Bool.and(reads(k, t, nm), Bool.not(own(at, slot)))
      +args = stray(kids, into(o, t, name, next, slot), slot, nm, name)
      +more = stray(rest, next, slot, nm, name)
      Bool.or(here, Bool.or(args, more))
    case Tree.NCons{+h, rest}:
      +head = stray(h, inner(at, slot), slot, nm, name)
      +more = stray(rest, past(Calls.kind.leaf(~Lex.is_comma, h), at), slot, nm, name)
      Bool.or(head, more)
    case Tree.Leaf{Lex.Tok{k, t, _l, _c}}:
      Bool.and(reads(k, t, nm), Bool.not(own(at, slot)))
    case Tree.Group{_o, kids, _cl}:
      stray(kids, at, slot, nm, name)
    case Tree.Stmt{_sk, kids, body}:
      +head = stray(kids, at, slot, nm, name)
      +more = stray(body, at, slot, nm, name)
      Bool.or(head, more)
    case Tree.NNil{}:
      False{}

# how many leaves under the node read the name
def spelled(n: Tree.Node, +nm: String) -> Nat:
  match n:
    case Tree.Leaf{Lex.Tok{k, t, _l, _c}}:
      Bool.pick(Nat, reads(k, t, nm), 1n, 0n)
    case Tree.Group{_o, kids, _cl}:
      spelled(kids, nm)
    case Tree.Stmt{_sk, kids, body}:
      Nat.add(spelled(kids, nm), spelled(body, nm))
    case Tree.NCons{h, t}:
      Nat.add(spelled(h, nm), spelled(t, nm))
    case Tree.NNil{}:
      0n

# a parameter's name token: its first lowercase name before the colon,
# none for a type parameter (`-A: Type`)
def named(p: Tree.Node) -> Maybe<&2, Lex.Tok>:
  match p:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, t, l, c}}, _rest}:
      Some{Lex.Tok{Lex.TName{}, t, l, c}}
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TColon{}, _t, _l, _c}}, _rest}:
      None{}
    case Tree.NCons{_h, rest}:
      named(rest)
    case _other:
      None{}

# may a parameter of this name be reported: typed, neither erased nor a
# template, and not named to be ignored?
def counts(p: Tree.Node, nm: String) -> Bool:
  Bool.and(Calls.is_live(p), Bool.not(String.starts_with(nm, "_")))

# is the parameter idle: one that counts, named once in the signature, read
# in the body, and never but in its own argument of a self-call?
def idle(p: Tree.Node, +slot: Nat, sig: Tree.Node, +body: Tree.Node, +nm: String, +name: String) -> Bool:
  +once = Nat.is_eq(spelled(sig, nm), 1n)
  +read = Bool.not(Nat.is_eq(spelled(body, nm), 0n))
  +kept = Bool.not(stray(body, AOut{}, slot, nm, name))
  Bool.and(counts(p, nm), Bool.and(once, Bool.and(read, kept)))

# what a finding says
def say(nm: String, name: String) -> String:
  "Parameter " ++ nm ++ " is read only where " ++ name ++ " passes it back to itself, so no result depends on it;"
    ++ " delete it, or read it where it was meant to count."

# the finding on the parameter's name
def cite(+nm: String, l: U32, c: U32, name: String, path: String) -> F.Finding:
  F.Finding{path, l, c, U32.from_nat(String.length(nm)), "idle", say(nm, name)}

# a finding on the parameter when it is idle, before the rest
def found(
  hit: Bool,
  nm: String,
  l: U32,
  c: U32,
  name: String,
  path: String,
  more: List<&2, F.Finding>
) -> List<&2, F.Finding>:
  match hit:
    case True{}:
      cite(nm, l, c, name, path) <> more
    case False{}:
      more

# a parameter with a name, judged; one with none adds nothing
def param(
  m: Maybe<&2, Lex.Tok>,
  p: Tree.Node,
  slot: Nat,
  sig: Tree.Node,
  body: Tree.Node,
  +name: String,
  path: String,
  more: List<&2, F.Finding>
) -> List<&2, F.Finding>:
  match m:
    case None{}:
      more
    case Some{Lex.Tok{_k, +nm, l, c}}:
      found(idle(p, slot, sig, body, nm, name), nm, l, c, name, path, more)

# the idle parameters among these, the first of them at this place, in
# order, before the rest
def params(
  ps: List<&2, Tree.Node>,
  +slot: Nat,
  +sig: Tree.Node,
  +body: Tree.Node,
  +name: String,
  +path: String,
  more: List<&2, F.Finding>
) -> List<&2, F.Finding>:
  match ps:
    case Nil{}:
      more
    case Con{+p, rest}:
      param(named(p), p, slot, sig, body, name, path, params(rest, 1n+slot, sig, body, name, path, more))

# is the def judged: not exempt, and one that calls itself?
def judged(path: String, sig: Tree.Node, body: Tree.Node, name: String) -> Bool:
  Bool.and(Bool.not(Calls.exempt(path, sig)), Calls.calls(body, name))

# every idle parameter of every def, in order
def check.go(ds: List<&2, Calls.Def>, +path: String) -> List<&2, F.Finding>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{Calls.Def{+name, +sig, +body}, rest}:
      +more = check.go(rest, path)
      Lazy.stop(List<&2, F.Finding>, Bool.not(judged(path, sig, body, name)), more,
        _u => params(Calls.params(sig), 0n, sig, body, name, path, more))

# the rule
def check(s: Src.Src) -> List<&2, F.Finding>:
  Src.Src{path, _text, _toks, tree, _bound, _items} = s
  check.go(Calls.defs(tree), path)
