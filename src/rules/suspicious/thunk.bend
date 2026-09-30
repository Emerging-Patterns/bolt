# rule thunk: a lambda whose body is exactly a self-call of its def, and
# whose parameter the call does not read, when it is the one lambda among the
# arguments of the call it is passed to: a `Unit -> T` thunk such as
# `Lazy.or_else(hit, _u => go(rest, k))`. The thunk is a closure allocated on
# every step, and the call inside it is not a tail call of the def, so the
# search leaves the loop each time round (bend 2.0.34, 500 misses over 100k
# cells: JS 2.40 s against 0.28 s, native 1.18 s against 0.76 s). Carry the
# test as a Bool into the next call instead, `go(rest, k, test(h))`, and match
# on it first: the step is then a tail call and compiles to a loop. `Lazy.*`
# stays right for guarding work that does not recurse. A dispatch, a call
# given two or more lambdas (`Lazy.either(T, c, _u => go(a), _v => go(b))`),
# is left alone: one Bool carried into the next call does not replace it.
# Exactly: in the kids of a group opened by `(` (its arguments: the kids split
# at their comma leaves), exactly one argument holding, among its own nodes
# and not inside a group, a leaf whose text is `=>`, four nodes in a row of
# those kids, a leaf whose kind is a name (the parameter: `_`, `_u`, `u`), a
# leaf whose text is `=>`, a leaf whose text is the def's name, and a `(`
# group; the kids end right after the group or go on with a comma; and no
# name leaf in the group, at any depth, has the parameter's text or starts
# with it and a dot (`u.x`). Groups are found at any depth, under statements
# and inside other groups, and a lambda inside another lambda's body is
# judged by the group it is passed to. One finding per such lambda, on the
# def's name. A body that does more than the call (`_u => go(t) ++ x`,
# `_u => Some{go(t)}`), a call of another def, a lambda whose parameter the
# call reads (an IO continuation `a => go(f, a)`), and a lambda that is not
# an argument of a call (`x = _u => go(t)`) are left alone; one that ignores
# its value (`_ => loop(n)`) is not, since the rule reads the shape and not
# the type. Laws and proofs never run: a law file, a proof file and a def
# that is a proof are exempt.
import Base
import ../../src.bend as Src
import ../../finding.bend as F
import ../../syntax/lex.bend as Lex
import ../../syntax/tree.bend as Tree
import ../calls.bend as Calls
import ../../lazy/lazy.bend as Lazy

# does a name leaf under the node read the parameter: its text, or its text
# then a dot?
def reads(nn: Tree.Node, +pp: String) -> Bool:
  match nn:
    case Tree.Leaf{Lex.Tok{k, +t, _l, _c}}:
      Bool.and(Lex.is_name(k), Bool.or(String.eq(t, pp), String.starts_with(t, pp ++ ".")))
    case Tree.Group{_o, kids, _cl}:
      reads(kids, pp)
    case Tree.Stmt{_k, kids, body}:
      +a = reads(kids, pp)
      +b = reads(body, pp)
      Bool.or(a, b)
    case Tree.NCons{h, t}:
      +a = reads(h, pp)
      +b = reads(t, pp)
      Bool.or(a, b)
    case Tree.NNil{}:
      False{}

# does the lambda's body end after the call: the chain ends, or a comma?
def ends(nn: Tree.Node) -> Bool:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, _t, _l, _c}}, _rest}:
      Lex.is_comma(k)
    case Tree.NCons{_h, _rest}:
      False{}
    case _other:
      True{}

# are the parts a thunk of a self-call: the lead (a name parameter the call
# does not read), `=>`, the def's name, a `(` group, then the body's end?
def hit(+lead: Bool, +arrow: Bool, +own: Bool, +call: Bool, +end: Bool) -> Bool:
  Bool.and(lead, Bool.and(arrow, Bool.and(own, Bool.and(call, end))))

# the finding at the self-call's name
def cite(+ll: U32, +cc: U32, +name: String, +path: String) -> F.Finding:
  F.Finding{path, ll, cc, U32.from_nat(String.length(name)), "thunk",
    name ++ " calls itself inside a thunk, which allocates a closure and leaves the loop on every step; carry the test as a Bool into the next call (`go(rest, k, test(h))`) and match on it first, so the search stays a loop."}

# after the parameter, `=>`, the name and its `(` group: the finding when
# they make a thunk of a self-call
def site.group(
  kp: Lex.TokKind,
  +pp: String,
  +aa: String,
  +nm: String,
  +ll: U32,
  +cc: U32,
  r3: Tree.Node,
  +name: String,
  +path: String
) -> List<&2, F.Finding>:
  match r3:
    case Tree.NCons{Tree.Group{Lex.Tok{_ko, +o, _lo, _co}, kids, _cl}, after}:
      +lead = Bool.and(Lex.is_name(kp), Bool.not(reads(kids, pp)))
      Bool.pick(List<&2, F.Finding>,
        hit(lead, String.eq(aa, "=>"), String.eq(nm, name), String.eq(o, "("), ends(after)),
        [cite(ll, cc, name, path)], [])
    case _other:
      []

# after the parameter and `=>`: the leaf that names the call
def site.name(
  kp: Lex.TokKind,
  +pp: String,
  +aa: String,
  r2: Tree.Node,
  +name: String,
  +path: String
) -> List<&2, F.Finding>:
  match r2:
    case Tree.NCons{Tree.Leaf{Lex.Tok{_kn, +n, +l, +c}}, r3}:
      site.group(kp, pp, aa, n, l, c, r3, name, path)
    case _other:
      []

# after the parameter: the leaf that should be `=>`
def site.lam(kp: Lex.TokKind, +pp: String, rest: Tree.Node, +name: String, +path: String) -> List<&2, F.Finding>:
  match rest:
    case Tree.NCons{Tree.Leaf{Lex.Tok{_ka, +a, _la, _ca}}, r2}:
      site.name(kp, pp, a, r2, name, path)
    case _other:
      []

# the finding when a node and the chain after it open a thunk of a self-call
def site(hh: Tree.Node, rest: Tree.Node, +name: String, +path: String) -> List<&2, F.Finding>:
  match hh:
    case Tree.Leaf{Lex.Tok{kp, +p, _l, _c}}:
      site.lam(kp, p, rest, name, path)
    case _other:
      []

# how many arguments of a group's kids, from here on, hold a `=>` leaf among
# their own nodes; seen: the argument under way does
def lams(nn: Tree.Node, +seen: Bool) -> Nat:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, t, _l, _c}}, rest}:
      +comma = Lex.is_comma(k)
      Nat.add(Bool.pick(Nat, Bool.and(comma, seen), 1n, 0n),
        lams(rest, Bool.and(Bool.not(comma), Bool.or(seen, String.eq(t, "=>")))))
    case Tree.NCons{_h, rest}:
      lams(rest, seen)
    case _other:
      Bool.pick(Nat, seen, 1n, 0n)

# is a group with this open and these kids a call given exactly one lambda?
def only(+oo: String, +kids: Tree.Node) -> Bool:
  Bool.and(String.eq(oo, "("), Nat.is_eq(lams(kids, False{}), 1n))

# every thunk of a self-call under the node, at any depth; lone: the node is
# the rest of the kids of a call given exactly one lambda
def walk(nn: Tree.Node, +lone: Bool, +name: String, +path: String) -> List<&2, F.Finding>:
  match nn:
    case Tree.NCons{+h, +rest}:
      +here = site(h, rest, name, path)
      List.concat(&2, F.Finding, [Bool.pick(List<&2, F.Finding>, lone, here, []),
        walk(h, False{}, name, path), walk(rest, lone, name, path)])
    case Tree.Group{Lex.Tok{_k, +o, _l, _c}, +kids, _cl}:
      walk(kids, only(o, kids), name, path)
    case Tree.Stmt{_k, kids, body}:
      List.concat(&2, F.Finding, [walk(kids, False{}, name, path), walk(body, False{}, name, path)])
    case _other:
      Nil{}

def check.go(ds: List<&2, Calls.Def>, +path: String, acc: List<&2, List<&2, F.Finding>>) -> List<&2, F.Finding>:
  match ds:
    case Nil{}:
      List.concat(&2, F.Finding, List.reverse(&2, List<&2, F.Finding>, acc))
    case Con{Calls.Def{+name, +sig, body}, rest}:
      check.go(rest, path,
        Lazy.stop(List<&2, F.Finding>, Calls.exempt(path, sig), [], _u => walk(body, False{}, name, path)) <> acc)

# the rule
def check(ss: Src.Src) -> List<&2, F.Finding>:
  Src.Src{path, text, toks, tree, bound, items} = ss
  check.go(Calls.defs(tree), path, [])
