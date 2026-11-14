# `concat` reports exactly a self-call argument that appends onto the
# parameter in its own position: the append written as the argument, inside
# any number of parentheses, or a lone name whose nearest `q = ..` or `+q =
# ..` let before the call, in its statement chain or an enclosing one, has
# such an append as its right side.
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/syntax/bind.bend as Bind
import ../src/src.bend as Src
import ../src/syntax/tree.bend as Tree
import ../src/syntax/outline.bend as Outline
import ../src/rules/suspicious/concat.bend as Concat
import ../src/rules/calls.bend as Calls

# concat (laws/ConcatReportsAppendingRecursion.bend). concat walks each def's body tree: a self-call is
# a leaf whose text is the def's name followed by a `(` group, its arguments
# are the group's kids split at top-level commas (Calls.args), and the
# parameter in an argument's position is the def's parameter at the same
# index ("" past the last, the same as an unnamed type parameter). The name
# an argument appends onto is Concat.seen's: Concat.onto's `p ++ ..`,
# `List.append(.., p, ..)` or `String.append(p, ..)` written as the argument,
# inside any number of parentheses, else a lone name's nearest let in scope
# (Concat.find). A let statement of one plain name (Concat.bound) is in scope
# for the statements after it in its chain, and for everything under them.

# True when the argument appends onto a name and that name is the slot's
def concat.is(m: Maybe<&2, Lex.Tok>, +slot: String) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{Lex.Tok{k, +t, l, c}}:
      String.eq(t, slot)

# how many arguments append onto the parameter in their own position
def concat.slots(as: List<&2, Tree.Node>, +params: List<&2, String>, +lets: List<&2, Concat.Let>) -> Nat:
  match as params:
    case Nil{} ps:
      0n
    case Con{+a, rest} Nil{}:
      +m = concat.slots(rest, Nil{}, lets)
      Bool.pick(Nat, concat.is(Concat.seen(a, lets), ""), 1n+m, m)
    case Con{+a, rest} Con{p, ps}:
      +m = concat.slots(rest, ps, lets)
      Bool.pick(Nat, concat.is(Concat.seen(a, lets), p), 1n+m, m)

# how many arguments of self-calls under the node append onto the parameter
# in their own position: a self-call's own arguments, then what its group and
# what follows it hold; a statement's let is in scope for what follows it
def concat.count(nn: Tree.Node, +name: String, +params: List<&2, String>, +lets: List<&2, Concat.Let>) -> Nat:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, +t, l, c}}, Tree.NCons{Tree.Group{Lex.Tok{_, +o, _, _}, +kids, _}, rest}}:
      +here = Bool.pick(Nat, Bool.and(String.eq(o, "("), String.eq(t, name)),
        concat.slots(Calls.args(kids), params, lets), 0n)
      Nat.add(here, Nat.add(concat.count(kids, name, params, lets), concat.count(rest, name, params, lets)))
    case Tree.NCons{Tree.Group{open, kids, close}, rest}:
      Nat.add(concat.count(kids, name, params, lets), concat.count(rest, name, params, lets))
    case Tree.NCons{Tree.Stmt{kind, +kids, body}, rest}:
      Nat.add(concat.count(kids, name, params, lets),
        Nat.add(concat.count(body, name, params, lets),
          concat.count(rest, name, params, Concat.after(kind, kids, lets))))
    case Tree.NCons{h, rest}:
      concat.count(rest, name, params, lets)
    case other:
      0n

# the count over a file's defs, none in a def that is exempt (a law file, a
# proof file, a def that returns a proof), each def starting with no lets
def concat.file(ds: List<&2, Calls.Def>, +path: String) -> Nat:
  match ds:
    case Nil{}:
      0n
    case Con{Calls.Def{+name, +sig, body}, rest}:
      Nat.add(Bool.pick(Nat, Calls.exempt(path, sig), 0n, concat.count(body, name, Calls.names(sig), [])),
        concat.file(rest, path))

# LAW: an argument in parentheses appends onto what its inside does
law concat_paren:
  for k: Lex.TokKind
  for l: U32
  for c: U32
  for kids: Tree.Node
  for cl: Maybe<&2, Lex.Tok>
  {Concat.onto(Tree.NCons{Tree.Group{Lex.Tok{k, "(", l, c}, kids, cl}, Tree.NNil{}}) == Concat.onto(kids)
    : Maybe<&2, Lex.Tok>}

# LAW: a lone name appends onto what its nearest let's right side does, and
# a let of the name shadows every one after it
law concat_nearest:
  for +name: String
  for m: Maybe<&2, Lex.Tok>
  for lets: List<&2, Concat.Let>
  {Concat.find(Concat.Let{name, m} <> lets, name) == m : Maybe<&2, Lex.Tok>}

# LAW: a let of another name is passed over
law concat_other:
  for +nm: String
  for +name: String
  for m: Maybe<&2, Lex.Tok>
  for lets: List<&2, Concat.Let>
  for e: {String.eq(nm, name) == False{} : Bool}
  {Concat.find(Concat.Let{nm, m} <> lets, name) == Concat.find(lets, name) : Maybe<&2, Lex.Tok>}

# LAW: a lone name is read through the lets
law concat_via:
  for +t: String
  for l: U32
  for c: U32
  for +lets: List<&2, Concat.Let>
  {Concat.seen(Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, t, l, c}}, Tree.NNil{}}, lets) == Concat.find(lets, t)
    : Maybe<&2, Lex.Tok>}

# LAW: an append written in place is read in place, whatever the lets say
law concat_in_place:
  for +a: Tree.Node
  for tok: Lex.Tok
  for lets: List<&2, Concat.Let>
  for e: {Concat.onto(a) == Some{tok} : Maybe<&2, Lex.Tok>}
  {Concat.seen(a, lets) == Some{tok} : Maybe<&2, Lex.Tok>}

# LAW: a let statement that binds one plain name puts it in scope, nearest
# first, for the statements after it
law concat_scope:
  for +kids: Tree.Node
  for lt: Concat.Let
  for lets: List<&2, Concat.Let>
  for e: {Concat.bound(kids) == Some{lt} : Maybe<&2, Concat.Let>}
  {Concat.after(Tree.SLet{}, kids, lets) == lt <> lets : List<&2, Concat.Let>}

# LAW: `+q = rhs` and `q = rhs` bind q to what rhs appends onto
law concat_bound:
  for +t: String
  for tl: U32
  for tc: U32
  for e: String
  for el: U32
  for ec: U32
  for +rhs: Tree.Node
  {Concat.bound(Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, t, tl, tc}},
    Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TEq{}, e, el, ec}}, rhs}}) == Some{Concat.Let{t, Concat.onto(rhs)}}
    : Maybe<&2, Concat.Let>}

# LAW: the `+` form binds the same way
law concat_bound_plus:
  for pl: U32
  for pc: U32
  for +t: String
  for tl: U32
  for tc: U32
  for e: String
  for el: U32
  for ec: U32
  for +rhs: Tree.Node
  {Concat.bound(Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TOp{}, "+", pl, pc}},
    Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, t, tl, tc}}, Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TEq{}, e, el, ec}}, rhs}}})
    == Some{Concat.Let{t, Concat.onto(rhs)}} : Maybe<&2, Concat.Let>}

# LAW: concat reports one finding for each self-call argument that appends
# onto the parameter in its own position, in every def its header does not
# exempt, and none for anything else
law concat_counts:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Concat.check(Src.Src{path, text, toks, tree, bound, items}))
    == concat.file(Calls.defs(tree), path) : Nat}
