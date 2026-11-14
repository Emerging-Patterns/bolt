# proofs of laws/ConcatReportsAppendingRecursion.bend
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/lazy/lazy.bend as Lazy
import ../src/syntax/tree.bend as Tree
import ../src/rules/calls.bend as Calls
import ../src/rules/correctness/pick.bend as Pick
import ../src/rules/suspicious/concat.bend as Concat
import ../laws/ConcatReportsAppendingRecursion.bend as Laws
import ./lemmas/ConcatSums.bend as M1
import ./lemmas/Nat.bend as M2
import ./lemmas/Pick.bend as M3
import ./lemmas/UnsafeStringCompare.bend as M4

# hit adds one finding exactly when the argument appends onto its slot
law concat.hit:
  for m: Maybe<&2, Lex.Tok>
  for +slot: String
  for +path: String
  for +acc: List<&2, F.Finding>
  {List.length(&2, F.Finding, Concat.hit(m, slot, path, acc))
    == Bool.pick(Nat, Laws.concat.is(m, slot), 1n+List.length(&2, F.Finding, acc), List.length(&2, F.Finding, acc))
    : Nat}

def concat.hit(m, slot, path, acc):
  match m:
    case None{}:
      {==}
    case Some{Lex.Tok{k, +t, l, c}}:
      M2.nat.pick(String.eq(t, slot), F.Finding{path, l, c, U32.from_nat(String.length(t)), "concat",
        t ++ " is appended to on every step, which copies it each time and makes the loop quadratic; prepend and reverse once at the end, or build with <>."},
        acc, List.length(&2, F.Finding, acc), {==})

# one argument's hit and the rest's, against its slot
law concat.arg:
  for +a: Tree.Node
  for +rest: List<&2, Tree.Node>
  for +slot: String
  for +ps: List<&2, String>
  for +lets: List<&2, Concat.Let>
  for +path: String
  for +acc: List<&2, F.Finding>
  for ih: {List.length(&2, F.Finding,
    Concat.hits(rest, ps, lets, path, Concat.hit(Concat.seen(a, lets), slot, path, acc)))
    == Nat.add(List.length(&2, F.Finding, Concat.hit(Concat.seen(a, lets), slot, path, acc)),
      Laws.concat.slots(rest, ps, lets)) : Nat}
  {List.length(&2, F.Finding, Concat.hits(rest, ps, lets, path, Concat.hit(Concat.seen(a, lets), slot, path, acc)))
    == Nat.add(List.length(&2, F.Finding, acc),
      Bool.pick(Nat, Laws.concat.is(Concat.seen(a, lets), slot), 1n+Laws.concat.slots(rest, ps, lets),
        Laws.concat.slots(rest, ps, lets))) : Nat}

def concat.arg(a, rest, slot, ps, lets, path, acc, ih):
  Equal.trans(Nat,
    List.length(&2, F.Finding, Concat.hits(rest, ps, lets, path, Concat.hit(Concat.seen(a, lets), slot, path, acc))),
    Nat.add(List.length(&2, F.Finding, Concat.hit(Concat.seen(a, lets), slot, path, acc)),
      Laws.concat.slots(rest, ps, lets)),
    Nat.add(List.length(&2, F.Finding, acc),
      Bool.pick(Nat, Laws.concat.is(Concat.seen(a, lets), slot), 1n+Laws.concat.slots(rest, ps, lets),
        Laws.concat.slots(rest, ps, lets))),
    ih,
    Equal.trans(Nat,
      Nat.add(List.length(&2, F.Finding, Concat.hit(Concat.seen(a, lets), slot, path, acc)),
        Laws.concat.slots(rest, ps, lets)),
      Nat.add(Bool.pick(Nat, Laws.concat.is(Concat.seen(a, lets), slot), 1n+List.length(&2, F.Finding, acc),
        List.length(&2, F.Finding, acc)), Laws.concat.slots(rest, ps, lets)),
      Nat.add(List.length(&2, F.Finding, acc),
        Bool.pick(Nat, Laws.concat.is(Concat.seen(a, lets), slot), 1n+Laws.concat.slots(rest, ps, lets),
          Laws.concat.slots(rest, ps, lets))),
      Equal.cong(Nat, Nat, n => Nat.add(n, Laws.concat.slots(rest, ps, lets)),
        List.length(&2, F.Finding, Concat.hit(Concat.seen(a, lets), slot, path, acc)),
        Bool.pick(Nat, Laws.concat.is(Concat.seen(a, lets), slot), 1n+List.length(&2, F.Finding, acc),
          List.length(&2, F.Finding, acc)),
        concat.hit(Concat.seen(a, lets), slot, path, acc)),
      M1.concat.bump(Laws.concat.is(Concat.seen(a, lets), slot), List.length(&2, F.Finding, acc),
        Laws.concat.slots(rest, ps, lets))))

# hits adds to its accumulator one finding for each argument that appends
# onto its own slot
law concat.hits:
  for as: List<&2, Tree.Node>
  for +params: List<&2, String>
  for +lets: List<&2, Concat.Let>
  for +path: String
  for +acc: List<&2, F.Finding>
  {List.length(&2, F.Finding, Concat.hits(as, params, lets, path, acc))
    == Nat.add(List.length(&2, F.Finding, acc), Laws.concat.slots(as, params, lets)) : Nat}

def concat.hits(as, params, lets, path, acc):
  match as:
    case Nil{}:
      M1.concat.rev(acc, Nil{})
    case Con{+a, +rest}:
      match params:
        case Nil{}:
          concat.arg(a, rest, "", Nil{}, lets, path, acc,
            concat.hits(rest, Nil{}, lets, path, Concat.hit(Concat.seen(a, lets), "", path, acc)))
        case Con{+p, +ps}:
          concat.arg(a, rest, p, ps, lets, path, acc,
            concat.hits(rest, ps, lets, path, Concat.hit(Concat.seen(a, lets), p, path, acc)))

# a leaf and a group: the self-call's hits, then the group's and the rest's
# counts, given the walk's law on the group's kids and on the rest
law concat.call:
  for tok: Lex.Tok
  for open: Lex.Tok
  for +kids: Tree.Node
  for cl: Maybe<&2, Lex.Tok>
  for +rest: Tree.Node
  for +name: String
  for +params: List<&2, String>
  for +lets: List<&2, Concat.Let>
  for +path: String
  for ik: {List.length(&2, F.Finding, Concat.walk(kids, name, params, lets, path))
    == Laws.concat.count(kids, name, params, lets) : Nat}
  for ir: {List.length(&2, F.Finding, Concat.walk(rest, name, params, lets, path))
    == Laws.concat.count(rest, name, params, lets) : Nat}
  {List.length(&2, F.Finding,
    Concat.walk(Tree.NCons{Tree.Leaf{tok}, Tree.NCons{Tree.Group{open, kids, cl}, rest}}, name, params, lets, path))
    == Laws.concat.count(Tree.NCons{Tree.Leaf{tok}, Tree.NCons{Tree.Group{open, kids, cl}, rest}}, name, params, lets)
    : Nat}

def concat.call(tok, open, kids, _cl, rest, name, params, lets, path, ik, ir):
  match tok open:
    case Lex.Tok{k, +t, l, c} Lex.Tok{ok, +o, ol, oc}:
      M1.concat.three(
        Lazy.stop(List<&2, F.Finding>, Bool.not(Bool.and(String.eq(o, "("), String.eq(t, name))), [],
          _u => Concat.hits(Calls.args(kids), params, lets, path, [])),
        Concat.walk(kids, name, params, lets, path), Concat.walk(rest, name, params, lets, path),
        Bool.pick(Nat, Bool.and(String.eq(o, "("), String.eq(t, name)),
          Laws.concat.slots(Calls.args(kids), params, lets), 0n),
        Laws.concat.count(kids, name, params, lets), Laws.concat.count(rest, name, params, lets),
        M1.concat.stop(Bool.and(String.eq(o, "("), String.eq(t, name)),
          Concat.hits(Calls.args(kids), params, lets, path, []),
          Laws.concat.slots(Calls.args(kids), params, lets), concat.hits(Calls.args(kids), params, lets, path, [])),
        ik, ir)

# walk finds what the law's count counts, node by node, whatever lets are in
# scope
law concat.walk:
  for n: Tree.Node
  for +name: String
  for +params: List<&2, String>
  for +lets: List<&2, Concat.Let>
  for +path: String
  {List.length(&2, F.Finding, Concat.walk(n, name, params, lets, path)) == Laws.concat.count(n, name, params, lets)
    : Nat}

def concat.walk(n, name, params, lets, path):
  match n:
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}}, Tree.NCons{Tree.Group{Lex.Tok{ok, o, ol, oc}, +kids, cl}, +rest}}:
      concat.call(Lex.Tok{k, t, l, c}, Lex.Tok{ok, o, ol, oc}, kids, cl, rest, name, params, lets, path,
        concat.walk(kids, name, params, lets, path), concat.walk(rest, name, params, lets, path))
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}}, Tree.NCons{Tree.Leaf{x}, rest}}:
      concat.walk(Tree.NCons{Tree.Leaf{x}, rest}, name, params, lets, path)
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}}, Tree.NCons{Tree.Stmt{kind, kids, body}, rest}}:
      concat.walk(Tree.NCons{Tree.Stmt{kind, kids, body}, rest}, name, params, lets, path)
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}}, Tree.NCons{Tree.NNil{}, rest}}:
      concat.walk(Tree.NCons{Tree.NNil{}, rest}, name, params, lets, path)
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}}, Tree.NCons{Tree.NCons{a, b}, rest}}:
      concat.walk(Tree.NCons{Tree.NCons{a, b}, rest}, name, params, lets, path)
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}}, Tree.Leaf{x}}:
      {==}
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}}, Tree.Group{open, kids, close}}:
      {==}
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}}, Tree.Stmt{kind, kids, body}}:
      {==}
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}}, Tree.NNil{}}:
      {==}
    case Tree.NCons{Tree.Group{open, +kids, close}, +rest}:
      M1.concat.two(Concat.walk(kids, name, params, lets, path), Concat.walk(rest, name, params, lets, path),
        Laws.concat.count(kids, name, params, lets), Laws.concat.count(rest, name, params, lets),
        concat.walk(kids, name, params, lets, path), concat.walk(rest, name, params, lets, path))
    case Tree.NCons{Tree.Stmt{+kind, +kids, +body}, +rest}:
      M1.concat.three(Concat.walk(kids, name, params, lets, path), Concat.walk(body, name, params, lets, path),
        Concat.walk(rest, name, params, Concat.after(kind, kids, lets), path),
        Laws.concat.count(kids, name, params, lets), Laws.concat.count(body, name, params, lets),
        Laws.concat.count(rest, name, params, Concat.after(kind, kids, lets)),
        concat.walk(kids, name, params, lets, path), concat.walk(body, name, params, lets, path),
        concat.walk(rest, name, params, Concat.after(kind, kids, lets), path))
    case Tree.NCons{Tree.NNil{}, rest}:
      concat.walk(rest, name, params, lets, path)
    case Tree.NCons{Tree.NCons{a, b}, rest}:
      concat.walk(rest, name, params, lets, path)
    case Tree.Leaf{x}:
      {==}
    case Tree.Group{open, kids, close}:
      {==}
    case Tree.Stmt{kind, kids, body}:
      {==}
    case Tree.NNil{}:
      {==}

# the def walk adds each def's count, none for an exempt def, to what its
# accumulator already holds
law concat.go:
  for ds: List<&2, Calls.Def>
  for +path: String
  for +acc: List<&2, List<&2, F.Finding>>
  {List.length(&2, F.Finding, Concat.check.go(ds, path, acc))
    == Nat.add(M1.concat.sum(acc), Laws.concat.file(ds, path)) : Nat}

def concat.go(ds, path, acc):
  match ds:
    case Nil{}:
      Equal.trans(Nat,
        List.length(&2, F.Finding, List.concat(&2, F.Finding, List.reverse(&2, List<&2, F.Finding>, acc))),
        M1.concat.sum(List.reverse.go(&2, List<&2, F.Finding>, acc, Nil{})), Nat.add(M1.concat.sum(acc), 0n),
        M1.concat.flat(List.reverse(&2, List<&2, F.Finding>, acc)), M1.concat.rsum(acc, Nil{}))
    case Con{Calls.Def{+name, +sig, +body}, +rest}:
      Equal.trans(Nat,
        List.length(&2, F.Finding, Concat.check.go(rest, path,
          Lazy.stop(List<&2, F.Finding>, Calls.exempt(path, sig), [],
            _u => Concat.walk(body, name, Calls.names(sig), [], path)) <> acc)),
        Nat.add(Nat.add(List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, Calls.exempt(path, sig), [],
          _u => Concat.walk(body, name, Calls.names(sig), [], path))), M1.concat.sum(acc)), Laws.concat.file(rest,
              path)),
        Nat.add(M1.concat.sum(acc),
          Nat.add(Bool.pick(Nat, Calls.exempt(path, sig), 0n, Laws.concat.count(body, name, Calls.names(sig), [])),
            Laws.concat.file(rest, path))),
        concat.go(rest, path, Lazy.stop(List<&2, F.Finding>, Calls.exempt(path, sig), [],
          _u => Concat.walk(body, name, Calls.names(sig), [], path)) <> acc),
        M1.concat.move(List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, Calls.exempt(path, sig), [],
            _u => Concat.walk(body, name, Calls.names(sig), [], path))),
          Bool.pick(Nat, Calls.exempt(path, sig), 0n, Laws.concat.count(body, name, Calls.names(sig), [])),
          M1.concat.sum(acc), Laws.concat.file(rest, path),
          M3.param.stop(Calls.exempt(path, sig), Concat.walk(body, name, Calls.names(sig), [], path),
            Laws.concat.count(body, name, Calls.names(sig), []),
            concat.walk(body, name, Calls.names(sig), [], path))))

def Laws.concat_counts(path, _text, _toks, tree, _bound, _items):
  concat.go(Calls.defs(tree), path, [])

def Laws.concat_paren(_k, _l, _c, _kids, _cl):
  {==}

def Laws.concat_via(_t, _l, _c, _lets):
  {==}

def Laws.concat_bound(_t, _tl, _tc, _e, _el, _ec, _rhs):
  {==}

def Laws.concat_in_place(a, tok, lets, e):
  %Equal.sym(Maybe<&2, Lex.Tok>, Concat.onto(a), Some{tok}, e) :
    {Concat.either(_, Concat.via(a, lets)) == Some{tok} : Maybe<&2, Lex.Tok>}
  {==}

def Laws.concat_scope(kids, lt, lets, e):
  %Equal.sym(Maybe<&2, Concat.Let>, Concat.bound(kids), Some{lt}, e) :
    {Concat.push(_, lets) == lt <> lets : List<&2, Concat.Let>}
  {==}

def Laws.concat_bound_plus(_pl, _pc, _t, _tl, _tc, _e, _el, _ec, _rhs):
  {==}

# concat_nearest and concat_other read String.eq on a let's name, so they
# sit below unsafe.srefl

def Laws.concat_nearest(name, m, lets):
  %Equal.sym(Bool, String.eq(name, name), True{}, M4.unsafe.srefl(name)) :
    {Lazy.stop(Maybe<&2, Lex.Tok>, _, m, _u => Concat.find(lets, name)) == m : Maybe<&2, Lex.Tok>}
  {==}

def Laws.concat_other(nm, name, m, lets, e):
  %Equal.sym(Bool, String.eq(nm, name), False{}, e) :
    {Lazy.stop(Maybe<&2, Lex.Tok>, _, m, _u => Concat.find(lets, name)) == Concat.find(lets, name)
      : Maybe<&2, Lex.Tok>}
  {==}
