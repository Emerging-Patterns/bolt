# proofs of laws/ConcatReportsContinuationAppend.bend
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/lazy/lazy.bend as Lazy
import ../src/paths.bend as Paths
import ../src/src.bend as Src
import ../src/syntax/tree.bend as Tree
import ../src/rules/calls.bend as Calls
import ../src/rules/suspicious/concat.bend as Concat
import ../laws/ConcatReportsContinuationAppend.bend as Laws
import ./lemmas/ConcatSums.bend as M1
import ./lemmas/Nat.bend as M2
import ./lemmas/Pick.bend as M3
import ./lemmas/LawFileExemptions.bend as M4

# hit.cont adds one finding exactly when the argument appends onto a
# reportable name
law cont.hit:
  for m: Maybe<&2, Lex.Tok>
  for +accs: List<&2, String>
  for +path: String
  for +acc: List<&2, F.Finding>
  {List.length(&2, F.Finding, Concat.hit.cont(m, accs, path, acc))
    == Bool.pick(Nat, Laws.cont.is(m, accs), 1n+List.length(&2, F.Finding, acc), List.length(&2, F.Finding, acc))
    : Nat}

def cont.hit(m, accs, path, acc):
  match m:
    case None{}:
      {==}
    case Some{Lex.Tok{k, +t, l, c}}:
      M2.nat.pick(List.contains(~String, ~String.eq, accs, t), F.Finding{path, l, c, U32.from_nat(String.length(t)),
        "concat",
        t ++ " is appended to and passed on through a continuation, which copies it on every step and makes the loop quadratic; prepend each chunk and reverse once at the end."},
        acc, List.length(&2, F.Finding, acc), {==})

# one argument's hit and the rest's
law cont.arg:
  for +a: Tree.Node
  for +rest: List<&2, Tree.Node>
  for +accs: List<&2, String>
  for +lets: List<&2, Concat.Let>
  for +path: String
  for +acc: List<&2, F.Finding>
  for ih: {List.length(&2, F.Finding,
    Concat.hits.cont(rest, accs, lets, path, Concat.hit.cont(Concat.seen(a, lets), accs, path, acc)))
    == Nat.add(List.length(&2, F.Finding, Concat.hit.cont(Concat.seen(a, lets), accs, path, acc)),
      Laws.cont.args(rest, accs, lets)) : Nat}
  {List.length(&2, F.Finding,
    Concat.hits.cont(rest, accs, lets, path, Concat.hit.cont(Concat.seen(a, lets), accs, path, acc)))
    == Nat.add(List.length(&2, F.Finding, acc),
      Bool.pick(Nat, Laws.cont.is(Concat.seen(a, lets), accs), 1n+Laws.cont.args(rest, accs, lets),
        Laws.cont.args(rest, accs, lets))) : Nat}

def cont.arg(a, rest, accs, lets, path, acc, ih):
  Equal.trans(Nat,
    List.length(&2, F.Finding,
      Concat.hits.cont(rest, accs, lets, path, Concat.hit.cont(Concat.seen(a, lets), accs, path, acc))),
    Nat.add(List.length(&2, F.Finding, Concat.hit.cont(Concat.seen(a, lets), accs, path, acc)),
      Laws.cont.args(rest, accs, lets)),
    Nat.add(List.length(&2, F.Finding, acc),
      Bool.pick(Nat, Laws.cont.is(Concat.seen(a, lets), accs), 1n+Laws.cont.args(rest, accs, lets),
        Laws.cont.args(rest, accs, lets))),
    ih,
    Equal.trans(Nat,
      Nat.add(List.length(&2, F.Finding, Concat.hit.cont(Concat.seen(a, lets), accs, path, acc)),
        Laws.cont.args(rest, accs, lets)),
      Nat.add(Bool.pick(Nat, Laws.cont.is(Concat.seen(a, lets), accs), 1n+List.length(&2, F.Finding, acc),
        List.length(&2, F.Finding, acc)), Laws.cont.args(rest, accs, lets)),
      Nat.add(List.length(&2, F.Finding, acc),
        Bool.pick(Nat, Laws.cont.is(Concat.seen(a, lets), accs), 1n+Laws.cont.args(rest, accs, lets),
          Laws.cont.args(rest, accs, lets))),
      Equal.cong(Nat, Nat, n => Nat.add(n, Laws.cont.args(rest, accs, lets)),
        List.length(&2, F.Finding, Concat.hit.cont(Concat.seen(a, lets), accs, path, acc)),
        Bool.pick(Nat, Laws.cont.is(Concat.seen(a, lets), accs), 1n+List.length(&2, F.Finding, acc),
          List.length(&2, F.Finding, acc)),
        cont.hit(Concat.seen(a, lets), accs, path, acc)),
      M1.concat.bump(Laws.cont.is(Concat.seen(a, lets), accs), List.length(&2, F.Finding, acc),
        Laws.cont.args(rest, accs, lets))))

# hits.cont adds to its accumulator one finding for each argument that
# appends onto a reportable name
law cont.hits:
  for as: List<&2, Tree.Node>
  for +accs: List<&2, String>
  for +lets: List<&2, Concat.Let>
  for +path: String
  for +acc: List<&2, F.Finding>
  {List.length(&2, F.Finding, Concat.hits.cont(as, accs, lets, path, acc))
    == Nat.add(List.length(&2, F.Finding, acc), Laws.cont.args(as, accs, lets)) : Nat}

def cont.hits(as, accs, lets, path, acc):
  match as:
    case Nil{}:
      M1.concat.rev(acc, Nil{})
    case Con{+a, +rest}:
      cont.arg(a, rest, accs, lets, path, acc,
        cont.hits(rest, accs, lets, path, Concat.hit.cont(Concat.seen(a, lets), accs, path, acc)))

# a leaf and a group: the continuation call's hits, then the group's and the
# rest's counts, given the walk's law on the group's kids and on the rest
law cont.call:
  for tok: Lex.Tok
  for open: Lex.Tok
  for +kids: Tree.Node
  for cl: Maybe<&2, Lex.Tok>
  for +rest: Tree.Node
  for +conts: List<&2, String>
  for +accs: List<&2, String>
  for +lets: List<&2, Concat.Let>
  for +path: String
  for ik: {List.length(&2, F.Finding, Concat.cwalk(kids, conts, accs, lets, path))
    == Laws.cont.count(kids, conts, accs, lets) : Nat}
  for ir: {List.length(&2, F.Finding, Concat.cwalk(rest, conts, accs, lets, path))
    == Laws.cont.count(rest, conts, accs, lets) : Nat}
  {List.length(&2, F.Finding,
    Concat.cwalk(Tree.NCons{Tree.Leaf{tok}, Tree.NCons{Tree.Group{open, kids, cl}, rest}}, conts, accs, lets, path))
    == Laws.cont.count(Tree.NCons{Tree.Leaf{tok}, Tree.NCons{Tree.Group{open, kids, cl}, rest}}, conts, accs, lets)
    : Nat}

def cont.call(tok, open, kids, _cl, rest, conts, accs, lets, path, ik, ir):
  match tok open:
    case Lex.Tok{k, +t, l, c} Lex.Tok{ok, +o, ol, oc}:
      M1.concat.three(
        Lazy.stop(List<&2, F.Finding>, Bool.not(Bool.and(String.eq(o, "("), List.contains(~String, ~String.eq, conts,
          t))), [], _u => Concat.hits.cont(Calls.args(kids), accs, lets, path, [])),
        Concat.cwalk(kids, conts, accs, lets, path), Concat.cwalk(rest, conts, accs, lets, path),
        Bool.pick(Nat, Bool.and(String.eq(o, "("), List.contains(~String, ~String.eq, conts, t)),
          Laws.cont.args(Calls.args(kids), accs, lets), 0n),
        Laws.cont.count(kids, conts, accs, lets), Laws.cont.count(rest, conts, accs, lets),
        M1.concat.stop(Bool.and(String.eq(o, "("), List.contains(~String, ~String.eq, conts, t)),
          Concat.hits.cont(Calls.args(kids), accs, lets, path, []),
          Laws.cont.args(Calls.args(kids), accs, lets), cont.hits(Calls.args(kids), accs, lets, path, [])),
        ik, ir)

# cwalk finds what the law's count counts, node by node, whatever lets are
# in scope
law cont.walk:
  for n: Tree.Node
  for +conts: List<&2, String>
  for +accs: List<&2, String>
  for +lets: List<&2, Concat.Let>
  for +path: String
  {List.length(&2, F.Finding, Concat.cwalk(n, conts, accs, lets, path)) == Laws.cont.count(n, conts, accs, lets)
    : Nat}

def cont.walk(n, conts, accs, lets, path):
  match n:
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}}, Tree.NCons{Tree.Group{Lex.Tok{ok, o, ol, oc}, +kids, cl}, +rest}}:
      cont.call(Lex.Tok{k, t, l, c}, Lex.Tok{ok, o, ol, oc}, kids, cl, rest, conts, accs, lets, path,
        cont.walk(kids, conts, accs, lets, path), cont.walk(rest, conts, accs, lets, path))
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}}, Tree.NCons{Tree.Leaf{x}, rest}}:
      cont.walk(Tree.NCons{Tree.Leaf{x}, rest}, conts, accs, lets, path)
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}}, Tree.NCons{Tree.Stmt{kind, kids, body}, rest}}:
      cont.walk(Tree.NCons{Tree.Stmt{kind, kids, body}, rest}, conts, accs, lets, path)
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}}, Tree.NCons{Tree.NNil{}, rest}}:
      cont.walk(Tree.NCons{Tree.NNil{}, rest}, conts, accs, lets, path)
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}}, Tree.NCons{Tree.NCons{a, b}, rest}}:
      cont.walk(Tree.NCons{Tree.NCons{a, b}, rest}, conts, accs, lets, path)
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}}, Tree.Leaf{x}}:
      {==}
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}}, Tree.Group{open, kids, close}}:
      {==}
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}}, Tree.Stmt{kind, kids, body}}:
      {==}
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}}, Tree.NNil{}}:
      {==}
    case Tree.NCons{Tree.Group{open, +kids, close}, +rest}:
      M1.concat.two(Concat.cwalk(kids, conts, accs, lets, path), Concat.cwalk(rest, conts, accs, lets, path),
        Laws.cont.count(kids, conts, accs, lets), Laws.cont.count(rest, conts, accs, lets),
        cont.walk(kids, conts, accs, lets, path), cont.walk(rest, conts, accs, lets, path))
    case Tree.NCons{Tree.Stmt{+kind, +kids, +body}, +rest}:
      M1.concat.three(Concat.cwalk(kids, conts, accs, lets, path), Concat.cwalk(body, conts, accs, lets, path),
        Concat.cwalk(rest, conts, accs, Concat.after(kind, kids, lets), path),
        Laws.cont.count(kids, conts, accs, lets), Laws.cont.count(body, conts, accs, lets),
        Laws.cont.count(rest, conts, accs, Concat.after(kind, kids, lets)),
        cont.walk(kids, conts, accs, lets, path), cont.walk(body, conts, accs, lets, path),
        cont.walk(rest, conts, accs, Concat.after(kind, kids, lets), path))
    case Tree.NCons{Tree.NNil{}, rest}:
      cont.walk(rest, conts, accs, lets, path)
    case Tree.NCons{Tree.NCons{a, b}, rest}:
      cont.walk(rest, conts, accs, lets, path)
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
law cont.go:
  for ds: List<&2, Calls.Def>
  for +path: String
  for +acc: List<&2, List<&2, F.Finding>>
  {List.length(&2, F.Finding, Concat.cont.go(ds, path, acc))
    == Nat.add(M1.concat.sum(acc), Laws.cont.file(ds, path)) : Nat}

def cont.go(ds, path, acc):
  match ds:
    case Nil{}:
      Equal.trans(Nat,
        List.length(&2, F.Finding, List.concat(&2, F.Finding, List.reverse(&2, List<&2, F.Finding>, acc))),
        M1.concat.sum(List.reverse.go(&2, List<&2, F.Finding>, acc, Nil{})), Nat.add(M1.concat.sum(acc), 0n),
        M1.concat.flat(List.reverse(&2, List<&2, F.Finding>, acc)), M1.concat.rsum(acc, Nil{}))
    case Con{Calls.Def{name, +sig, +body}, +rest}:
      Equal.trans(Nat,
        List.length(&2, F.Finding, Concat.cont.go(rest, path,
          Lazy.stop(List<&2, F.Finding>, Calls.exempt(path, sig), [],
            _u => Concat.cwalk(body, Concat.conts(sig), Concat.accs(sig, body), [], path)) <> acc)),
        Nat.add(Nat.add(List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, Calls.exempt(path, sig), [],
          _u => Concat.cwalk(body, Concat.conts(sig), Concat.accs(sig, body), [], path))), M1.concat.sum(acc)),
          Laws.cont.file(rest, path)),
        Nat.add(M1.concat.sum(acc),
          Nat.add(Bool.pick(Nat, Calls.exempt(path, sig), 0n,
            Laws.cont.count(body, Concat.conts(sig), Concat.accs(sig, body), [])), Laws.cont.file(rest, path))),
        cont.go(rest, path, Lazy.stop(List<&2, F.Finding>, Calls.exempt(path, sig), [],
          _u => Concat.cwalk(body, Concat.conts(sig), Concat.accs(sig, body), [], path)) <> acc),
        M1.concat.move(List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, Calls.exempt(path, sig), [],
            _u => Concat.cwalk(body, Concat.conts(sig), Concat.accs(sig, body), [], path))),
          Bool.pick(Nat, Calls.exempt(path, sig), 0n,
            Laws.cont.count(body, Concat.conts(sig), Concat.accs(sig, body), [])),
          M1.concat.sum(acc), Laws.cont.file(rest, path),
          M3.param.stop(Calls.exempt(path, sig),
            Concat.cwalk(body, Concat.conts(sig), Concat.accs(sig, body), [], path),
            Laws.cont.count(body, Concat.conts(sig), Concat.accs(sig, body), []),
            cont.walk(body, Concat.conts(sig), Concat.accs(sig, body), [], path))))

def Laws.concat_cont_counts(path, _text, _toks, tree, _bound, _items):
  cont.go(Calls.defs(tree), path, [])

def Laws.concat_keep_plain(n):
  match n:
    case 0n:
      {==}
    case 1n+m:
      match m:
        case 0n:
          {==}
        case 1n+_k:
          {==}

def Laws.concat_keep_once(_b):
  {==}

def Laws.concat_keep_reused(_n):
  {==}

def Laws.concat_plus(_l, _c, _rest):
  {==}

def Laws.concat_conts(p, ps, acc, e):
  %Equal.sym(Bool, Calls.has_arrow(p), True{}, e) :
    {Concat.conts.go(ps, Bool.pick(List<&2, String>, _, Calls.param_name(p) <> acc, acc))
      == Concat.conts.go(ps, Calls.param_name(p) <> acc) : List<&2, String>}
  {==}

def Laws.concat_not_cont(p, ps, acc, e):
  %Equal.sym(Bool, Calls.has_arrow(p), False{}, e) :
    {Concat.conts.go(ps, Bool.pick(List<&2, String>, _, Calls.param_name(p) <> acc, acc))
      == Concat.conts.go(ps, acc) : List<&2, String>}
  {==}

# the continuation half's def walk gathers nothing in a law file
law cont.exempt:
  for ds: List<&2, Calls.Def>
  for +path: String
  for +n: Nat
  for +e: {Paths.is_law_file(path) == True{} : Bool}
  {Concat.cont.go(ds, path, M4.ex.rep(n)) == Nil{} : List<&2, F.Finding>}

def cont.exempt(ds, path, n, e):
  match ds:
    case Nil{}:
      M4.ex.flat(n, Nil{})
    case Con{Calls.Def{name, +sig, +body}, rest}:
      M4.ex.push(
        Calls.exempt(path, sig),
        M4.ex.calls(path, sig, e),
        _u => Concat.cwalk(body, Concat.conts(sig), Concat.accs(sig, body), [], path), n,
        v => Concat.cont.go(rest, path, v), cont.exempt(rest, path, 1n+n, e))

def Laws.concat_cont_exempt(path, _text, _toks, tree, _bound, _items, e):
  cont.exempt(Calls.defs(tree), path, 0n, e)

def Laws.role_concat_cont(path, text, toks, tree, bound, items):
  M4.role.skip_named(path, _u => Concat.cont(Src.Src{path, text, toks, tree, bound, items}),
    e => Laws.concat_cont_exempt(path, text, toks, tree, bound, items, e))
