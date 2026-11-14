# `thunk` (opt-in) reports exactly, in a def, a lambda whose body is exactly a
# self-call and whose parameter that call does not read, passed as the one
# lambda of a call: in the kids of a group opened by `(` (its arguments: the
# kids split at their comma leaves), exactly one argument holding, among its
# own nodes and not inside a group, a leaf whose text is `=>`, four nodes in a
# row of those kids, a leaf of a name kind (the parameter), a leaf whose text
# is `=>`, a leaf whose text is the def's name, and a `(` group, the kids
# ending right after the group or going on with a comma, and no name leaf in
# the group, at any depth, spelling the parameter or the parameter then a dot;
# such groups found at any depth; one finding for each, on the def's name, and
# nothing else. A call given two or more lambdas (a dispatch) gets none.
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/syntax/bind.bend as Bind
import ../src/src.bend as Src
import ../src/syntax/tree.bend as Tree
import ../src/syntax/outline.bend as Outline
import ../src/rules/suspicious/thunk.bend as Thunk
import ../src/rules/calls.bend as Calls

# thunk (laws/ThunkReportsIgnoredSelfCallLambdas.bend). A thunk of a self-call is read off the kids of a
# call given one lambda: a group opened by `(` whose kids, split at their
# comma leaves, hold exactly one argument with a leaf whose text is `=>`
# among its own nodes. In those kids, its first node a leaf of a name kind
# (the parameter), then a leaf whose text is `=>`, then a leaf whose text is
# the def's name, then a group opened by `(`, and after the group the kids'
# end or a comma. The group must not read the parameter: no name leaf under
# it, at any depth, spells the parameter, or the parameter then a dot. Such
# calls are found at any depth. Each def of the file that is not exempt
# counts the thunks of its body.

# does a name leaf under the node spell the parameter, or it then a dot?
def thunk.reads(n: Tree.Node, +p: String) -> Bool:
  match n:
    case Tree.Leaf{Lex.Tok{k, +t, l, c}}:
      Bool.and(Lex.is_name(k), Bool.or(String.eq(t, p), String.starts_with(t, p ++ ".")))
    case Tree.Group{o, kids, cl}:
      thunk.reads(kids, p)
    case Tree.Stmt{sk, kids, body}:
      Bool.or(thunk.reads(kids, p), thunk.reads(body, p))
    case Tree.NCons{h, t}:
      Bool.or(thunk.reads(h, p), thunk.reads(t, p))
    case Tree.NNil{}:
      False{}

# is what follows the call the chain's end, or a comma?
def thunk.last(n: Tree.Node) -> Bool:
  match n:
    case Tree.NCons{h, t}:
      Calls.kind.leaf(~Lex.is_comma, h)
    case other:
      True{}

# the rest past the name: a `(` group that does not read the parameter, then
# the body's end
def thunk.call(kp: Lex.TokKind, +p: String, +a: String, +nm: String, r3: Tree.Node, +name: String) -> Bool:
  match r3:
    case Tree.NCons{Tree.Group{Lex.Tok{ko, o, lo, co}, kids, cl}, after}:
      Bool.and(Bool.and(Lex.is_name(kp), Bool.not(thunk.reads(kids, p))),
        Bool.and(String.eq(a, "=>"), Bool.and(String.eq(nm, name), Bool.and(String.eq(o, "("), thunk.last(after)))))
    case other:
      False{}

# the rest past `=>`: a leaf, the name called
def thunk.callee(kp: Lex.TokKind, +p: String, +a: String, r2: Tree.Node, +name: String) -> Bool:
  match r2:
    case Tree.NCons{Tree.Leaf{Lex.Tok{kn, n, ln, cn}}, r3}:
      thunk.call(kp, p, a, n, r3, name)
    case other:
      False{}

# the rest past the parameter: a leaf, the arrow
def thunk.lam(kp: Lex.TokKind, +p: String, r: Tree.Node, +name: String) -> Bool:
  match r:
    case Tree.NCons{Tree.Leaf{Lex.Tok{ka, a, la, ca}}, r2}:
      thunk.callee(kp, p, a, r2, name)
    case other:
      False{}

# does the chain open with a thunk of a self-call of the name?
def thunk.at(n: Tree.Node, +name: String) -> Bool:
  match n:
    case Tree.NCons{Tree.Leaf{Lex.Tok{kp, p, lp, cp}}, r}:
      thunk.lam(kp, p, r, name)
    case other:
      False{}

# the arguments of the chain, from here on, that hold a `=>` leaf among their
# own nodes (a comma leaf ends one); seen: the one under way does
def thunk.args(nn: Tree.Node, +seen: Bool) -> Nat:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{+k, t, l, c}}, rest}:
      Nat.add(Bool.pick(Nat, Bool.and(Lex.is_comma(k), seen), 1n, 0n),
        thunk.args(rest, Bool.and(Bool.not(Lex.is_comma(k)), Bool.or(seen, String.eq(t, "=>")))))
    case Tree.NCons{h, rest}:
      thunk.args(rest, seen)
    case other:
      Bool.pick(Nat, seen, 1n, 0n)

# is a group opened by o over the kids a call given exactly one lambda?
def thunk.lone(+o: String, +kids: Tree.Node) -> Bool:
  Bool.and(String.eq(o, "("), Nat.is_eq(thunk.args(kids, False{}), 1n))

# how many thunks of a self-call of the name the node holds, at any depth,
# each in the kids of a call given one lambda; lone: the node is the rest of
# such kids
def thunk.count(nn: Tree.Node, +lone: Bool, +name: String) -> Nat:
  match nn:
    case Tree.NCons{+h, +rest}:
      Nat.add(Bool.pick(Nat, Bool.and(lone, thunk.at(Tree.NCons{h, rest}, name)), 1n, 0n),
        Nat.add(thunk.count(h, False{}, name), thunk.count(rest, lone, name)))
    case Tree.Group{Lex.Tok{k, +o, l, c}, +kids, cl}:
      thunk.count(kids, thunk.lone(o, kids), name)
    case Tree.Stmt{sk, kids, body}:
      Nat.add(thunk.count(kids, False{}, name), thunk.count(body, False{}, name))
    case other:
      0n

# LAW: over any node, thunk reports one finding for each thunk of a
# self-call passed as the one lambda of a call, and none for anything else
law thunk_walk_counts:
  for n: Tree.Node
  for +lone: Bool
  for +name: String
  for +path: String
  {List.length(&2, F.Finding, Thunk.walk(n, lone, name, path)) == thunk.count(n, lone, name) : Nat}

# the thunks of a self-call in each def of the list that is not exempt
def thunk.defs(ds: List<&2, Calls.Def>, +path: String) -> Nat:
  match ds:
    case Nil{}:
      0n
    case Con{Calls.Def{+name, +sig, +body}, rest}:
      Nat.add(Bool.pick(Nat, Calls.exempt(path, sig), 0n, thunk.count(body, False{}, name)), thunk.defs(rest, path))

# LAW: thunk reports exactly those, def by def, over the defs of the tree
law thunk_counts:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Thunk.check(Src.Src{path, text, toks, tree, bound, items}))
    == thunk.defs(Calls.defs(tree), path) : Nat}
