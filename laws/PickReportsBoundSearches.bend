# `pick` also reports exactly, in a def, a first-match search that binds its
# own call above the pick: in one chain of statements (a def's body, or the
# body of one statement under it, such as a case arm), a let whose own tokens
# are, past a leading `+`, a leaf of a name kind (the bound name), a leaf
# whose text is `=`, a leaf whose text is the def's name and a `(` group,
# nothing after it; and the first statement after the let, in that chain,
# with a name leaf spelling the bound name is a statement whose own tokens
# are a leaf whose text is `Bool.pick` and a `(` group, nothing after it,
# whose condition (its second argument) and then branch (its third) have no
# such leaf and whose else branch (its fourth) has one; and the self-call's
# group holds, at any depth, no `Bool.pick(..)` whose condition has the same
# text as this pick's. One finding for each such let, on the def's name, and
# nothing else. So a do-bind (`x <- f(..)`, no `=`), a let and a pick in
# different chains (two case arms), and a call made cheap on purpose by a
# pick on the same condition are not reported; nor is anything in a law or
# proof file, or in a def that is a proof.
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/syntax/bind.bend as Bind
import ../src/paths.bend as Paths
import ../src/src.bend as Src
import ../src/syntax/tree.bend as Tree
import ../src/syntax/outline.bend as Outline
import ../src/rules/correctness/pick.bend as Pick
import ../src/rules/calls.bend as Calls

# does a name leaf under the node spell x?
def search.reads(n: Tree.Node, +x: String) -> Bool:
  match n:
    case Tree.Leaf{Lex.Tok{k, +t, l, c}}:
      Bool.and(Lex.is_name(k), String.eq(t, x))
    case Tree.Group{o, kids, cl}:
      search.reads(kids, x)
    case Tree.Stmt{sk, kids, body}:
      Bool.or(search.reads(kids, x), search.reads(body, x))
    case Tree.NCons{h, t}:
      Bool.or(search.reads(h, x), search.reads(t, x))
    case Tree.NNil{}:
      False{}

# the first node of the chain that reads x, NNil when none does
def search.first(n: Tree.Node, +x: String) -> Tree.Node:
  match n:
    case Tree.NCons{+h, t}:
      Bool.pick(Tree.Node, search.reads(h, x), h, search.first(t, x))
    case other:
      Tree.NNil{}

# does a `Bool.pick(..)` under the node, at any depth, have a condition (its
# second argument) whose text (Pick.search.text) is cond?
def search.same(nn: Tree.Node, +cond: String) -> Bool:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, +t, l, c}}, Tree.NCons{Tree.Group{Lex.Tok{ko, +o, lo, co}, +kids, cl}, rest}}:
      Bool.or(Bool.and(Bool.and(String.eq(t, "Bool.pick"), String.eq(o, "(")),
        String.eq(Pick.search.text(Calls.arg(Calls.args(kids), 1n)), cond)),
        Bool.or(search.same(kids, cond), search.same(rest, cond)))
    case Tree.Group{o, kids, cl}:
      search.same(kids, cond)
    case Tree.Stmt{sk, kids, body}:
      Bool.or(search.same(kids, cond), search.same(body, cond))
    case Tree.NCons{h, t}:
      Bool.or(search.same(h, cond), search.same(t, cond))
    case other:
      False{}

# is the chain empty?
def search.none(n: Tree.Node) -> Bool:
  match n:
    case Tree.NNil{}:
      True{}
    case other:
      False{}

# is a pick's argument list (as) one that reads x in its else branch only?
def search.only(+as: List<&2, Tree.Node>, +x: String) -> Bool:
  Bool.and(Bool.not(Bool.or(search.reads(Calls.arg(as, 1n), x), search.reads(Calls.arg(as, 2n), x))),
    search.reads(Calls.arg(as, 3n), x))

# is the statement a `Bool.pick(..)` alone that reads x in its else branch
# only, on a condition no pick in the self-call's group (args) has?
def search.pick(s: Tree.Node, +x: String, +args: Tree.Node) -> Bool:
  match s:
    case Tree.Stmt{sk, Tree.NCons{Tree.Leaf{Lex.Tok{kt, +t, lt, ct}}, Tree.NCons{Tree.Group{Lex.Tok{ko, +o, lo, co},
      +kids, cl}, after}}, body}:
      Bool.and(Bool.and(Bool.and(Bool.and(String.eq(t, "Bool.pick"), String.eq(o, "(")), search.none(after)),
        search.only(Calls.args(kids), x)),
        Bool.not(search.same(args, Pick.search.text(Calls.arg(Calls.args(kids), 1n)))))
    case other:
      False{}

# past a let's bound name: `=`, the def's name, a `(` group and nothing
# after it, and the first reader of the name in rest a pick that the bound
# call makes a search of
def search.call(kx: Lex.TokKind, +x: String, r1: Tree.Node, rest: Tree.Node, +name: String) -> Bool:
  match r1:
    case Tree.NCons{Tree.Leaf{Lex.Tok{ke, +e, le, ce}}, Tree.NCons{Tree.Leaf{Lex.Tok{kn, +n, ln, cn}},
      Tree.NCons{Tree.Group{Lex.Tok{ko, +o, lo, co}, +args, cl}, after}}}:
      Bool.and(Bool.and(Bool.and(Lex.is_name(kx), String.eq(e, "=")),
        Bool.and(Bool.and(String.eq(n, name), String.eq(o, "(")), search.none(after))),
        search.pick(search.first(rest, x), x, args))
    case other:
      False{}

# a let's own tokens past a leading `+`: the bound name, then the call
def search.bound(n: Tree.Node, rest: Tree.Node, +name: String) -> Bool:
  match n:
    case Tree.NCons{Tree.Leaf{Lex.Tok{kx, +x, lx, cx}}, r1}:
      search.call(kx, x, r1, rest, name)
    case other:
      False{}

# a let's own tokens, the leading `+` skipped when there is one
def search.plus(kids: Tree.Node) -> Tree.Node:
  match kids:
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, +t, l, c}}, +more}:
      Bool.pick(Tree.Node, String.eq(t, "+"), more, Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}}, more})
    case other:
      Tree.NNil{}

# is a statement of the kind and own tokens, the chain after it rest, a let
# that binds a search above its pick?
def search.at(kind: Tree.StmtKind, kids: Tree.Node, rest: Tree.Node, +name: String) -> Bool:
  match kind:
    case Tree.SLet{}:
      search.bound(search.plus(kids), rest, name)
    case other:
      False{}

# how many lets in a chain of statements, and in the chains under them,
# bind a search above its pick
def search.count(nn: Tree.Node, +name: String) -> Nat:
  match nn:
    case Tree.NCons{Tree.Stmt{kind, kids, body}, +rest}:
      Nat.add(Bool.pick(Nat, search.at(kind, kids, rest, name), 1n, 0n),
        Nat.add(search.count(body, name), search.count(rest, name)))
    case Tree.NCons{h, rest}:
      search.count(rest, name)
    case other:
      0n

# LAW: over any chain, pick reports one finding for each let that binds a
# search above its pick, and nothing else
law pick_search_walk_counts:
  for n: Tree.Node
  for +name: String
  for +path: String
  {List.length(&2, F.Finding, Pick.search.walk(n, name, path)) == search.count(n, name) : Nat}

# the searches bound above their picks in each def of the list that is not
# exempt
def search.defs(ds: List<&2, Calls.Def>, +path: String) -> Nat:
  match ds:
    case Nil{}:
      0n
    case Con{Calls.Def{+name, +sig, +body}, rest}:
      Nat.add(Bool.pick(Nat, Calls.exempt(path, sig), 0n, search.count(body, name)), search.defs(rest, path))

# LAW: pick reports exactly those, def by def, over the defs of the tree
law pick_search_counts:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Pick.search(Src.Src{path, text, toks, tree, bound, items}))
    == search.defs(Calls.defs(tree), path) : Nat}

# LAW: pick reports no bound search in a LAWS.bend or a PROOF.bend, which
# never run, whatever the source holds
law pick_search_exempt:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  for e: {Paths.is_law_file(path) == True{} : Bool}
  {Pick.search(Src.Src{path, text, toks, tree, bound, items}) == Nil{} : List<&2, F.Finding>}
