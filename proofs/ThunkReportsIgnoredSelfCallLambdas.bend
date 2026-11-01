# proofs of laws/ThunkReportsIgnoredSelfCallLambdas.bend
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/lazy/lazy.bend as Lazy
import ../src/syntax/tree.bend as Tree
import ../src/rules/calls.bend as Calls
import ../src/rules/correctness/pick.bend as Pick
import ../src/rules/suspicious/thunk.bend as Thunk
import ../laws/ThunkReportsIgnoredSelfCallLambdas.bend as Laws
import ./lemmas/Pick.bend as M1

# thunk (laws/ThunkReportsIgnoredSelfCallLambdas.bend). The rule's reads, ends and lams agree with the
# law's by induction and by one split; each site helper agrees with the law's
# step of the same place, so a site gives one finding exactly when the law's
# chain opens a thunk, and a gated site exactly when the kids are a call's
# with one lambda; the walk and the def walk then add up as unit's do.

# the rule's reads is the law's
law thunk.reads:
  for nn: Tree.Node
  for +pp: String
  {Thunk.reads(nn, pp) == Laws.thunk.reads(nn, pp) : Bool}

def thunk.reads(nn, pp):
  match nn:
    case Tree.Leaf{tok}:
      match tok:
        case Lex.Tok{k, t, l, c}:
          {==}
    case Tree.Group{o, +kids, cl}:
      thunk.reads(kids, pp)
    case Tree.Stmt{sk, +kids, +body}:
      %thunk.reads(kids, pp) : {Bool.or(Thunk.reads(kids, pp), Thunk.reads(body, pp))
        == Bool.or(_, Laws.thunk.reads(body, pp)) : Bool}
      %thunk.reads(body, pp) : {Bool.or(Thunk.reads(kids, pp), Thunk.reads(body, pp))
        == Bool.or(Thunk.reads(kids, pp), _) : Bool}
      {==}
    case Tree.NCons{+h, +t}:
      %thunk.reads(h, pp) : {Bool.or(Thunk.reads(h, pp), Thunk.reads(t, pp))
        == Bool.or(_, Laws.thunk.reads(t, pp)) : Bool}
      %thunk.reads(t, pp) : {Bool.or(Thunk.reads(h, pp), Thunk.reads(t, pp))
        == Bool.or(Thunk.reads(h, pp), _) : Bool}
      {==}
    case Tree.NNil{}:
      {==}

# the rule's end of a body is the law's
law thunk.ends:
  for nn: Tree.Node
  {Thunk.ends(nn) == Laws.thunk.last(nn) : Bool}

def thunk.ends(nn):
  match nn:
    case Tree.NCons{h, t}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{k, s, l, c}: {==}
        case Tree.Group{a, b, c}: {==}
        case Tree.Stmt{a, b, c}: {==}
        case Tree.NNil{}: {==}
        case Tree.NCons{a, b}: {==}
    case Tree.Leaf{x}: {==}
    case Tree.Group{a, b, c}: {==}
    case Tree.Stmt{a, b, c}: {==}
    case Tree.NNil{}: {==}

# past the name: the rule's finding is the law's count
law thunk.site.group:
  for kp: Lex.TokKind
  for +pp: String
  for +aa: String
  for +nm: String
  for +ll: U32
  for +cc: U32
  for r3: Tree.Node
  for +name: String
  for +path: String
  {List.length(&2, F.Finding, Thunk.site.group(kp, pp, aa, nm, ll, cc, r3, name, path))
    == Bool.pick(Nat, Laws.thunk.call(kp, pp, aa, nm, r3, name), 1n, 0n) : Nat}

def thunk.site.group(kp, pp, aa, nm, ll, cc, r3, name, path):
  match r3:
    case Tree.NCons{h, +after}:
      match h:
        case Tree.Group{open, +kids, cl}:
          match open:
            case Lex.Tok{ko, +o, lo, co}:
              +f = Thunk.cite(ll, cc, name, path)
              +b = Thunk.hit(Bool.and(Lex.is_name(kp), Bool.not(Thunk.reads(kids, pp))), String.eq(aa, "=>"),
                String.eq(nm, name), String.eq(o, "("), Thunk.ends(after))
              %thunk.reads(kids, pp) : {List.length(&2, F.Finding, Bool.pick(List<&2, F.Finding>, b, [f], []))
                == Bool.pick(Nat, Bool.and(Bool.and(Lex.is_name(kp), Bool.not(_)), Bool.and(String.eq(aa, "=>"),
                  Bool.and(String.eq(nm, name), Bool.and(String.eq(o, "("), Laws.thunk.last(after))))), 1n, 0n) : Nat}
              %thunk.ends(after) : {List.length(&2, F.Finding, Bool.pick(List<&2, F.Finding>, b, [f], []))
                == Bool.pick(Nat, Bool.and(Bool.and(Lex.is_name(kp), Bool.not(Thunk.reads(kids, pp))),
                  Bool.and(String.eq(aa, "=>"), Bool.and(String.eq(nm, name), Bool.and(String.eq(o, "("), _)))), 1n,
                  0n) : Nat}
              M1.thunk.one(b, f)
        case Tree.Leaf{x}: {==}
        case Tree.Stmt{x, y, z}: {==}
        case Tree.NNil{}: {==}
        case Tree.NCons{x, y}: {==}
    case Tree.Leaf{x}: {==}
    case Tree.Group{x, y, z}: {==}
    case Tree.Stmt{x, y, z}: {==}
    case Tree.NNil{}: {==}

# past `=>`: the rule's finding is the law's count
law thunk.site.name:
  for kp: Lex.TokKind
  for +pp: String
  for +aa: String
  for r2: Tree.Node
  for +name: String
  for +path: String
  {List.length(&2, F.Finding, Thunk.site.name(kp, pp, aa, r2, name, path))
    == Bool.pick(Nat, Laws.thunk.callee(kp, pp, aa, r2, name), 1n, 0n) : Nat}

def thunk.site.name(kp, pp, aa, r2, name, path):
  match r2:
    case Tree.NCons{h, r3}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{kn, n, l, c}: thunk.site.group(kp, pp, aa, n, l, c, r3, name, path)
        case Tree.Group{x, y, z}: {==}
        case Tree.Stmt{x, y, z}: {==}
        case Tree.NNil{}: {==}
        case Tree.NCons{x, y}: {==}
    case Tree.Leaf{x}: {==}
    case Tree.Group{x, y, z}: {==}
    case Tree.Stmt{x, y, z}: {==}
    case Tree.NNil{}: {==}

# past the parameter: the rule's finding is the law's count
law thunk.site.lam:
  for kp: Lex.TokKind
  for +pp: String
  for rest: Tree.Node
  for +name: String
  for +path: String
  {List.length(&2, F.Finding, Thunk.site.lam(kp, pp, rest, name, path))
    == Bool.pick(Nat, Laws.thunk.lam(kp, pp, rest, name), 1n, 0n) : Nat}

def thunk.site.lam(kp, pp, rest, name, path):
  match rest:
    case Tree.NCons{h, r2}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{ka, a, l, c}: thunk.site.name(kp, pp, a, r2, name, path)
        case Tree.Group{x, y, z}: {==}
        case Tree.Stmt{x, y, z}: {==}
        case Tree.NNil{}: {==}
        case Tree.NCons{x, y}: {==}
    case Tree.Leaf{x}: {==}
    case Tree.Group{x, y, z}: {==}
    case Tree.Stmt{x, y, z}: {==}
    case Tree.NNil{}: {==}

# a node and the chain after it: the rule's finding is the law's count
law thunk.site:
  for hh: Tree.Node
  for rest: Tree.Node
  for +name: String
  for +path: String
  {List.length(&2, F.Finding, Thunk.site(hh, rest, name, path))
    == Bool.pick(Nat, Laws.thunk.at(Tree.NCons{hh, rest}, name), 1n, 0n) : Nat}

def thunk.site(hh, rest, name, path):
  match hh:
    case Tree.Leaf{tok}:
      match tok:
        case Lex.Tok{kp, p, l, c}: thunk.site.lam(kp, p, rest, name, path)
    case Tree.Group{x, y, z}: {==}
    case Tree.Stmt{x, y, z}: {==}
    case Tree.NNil{}: {==}
    case Tree.NCons{x, y}: {==}

# the rule's count of lambda arguments is the law's
law thunk.lams:
  for nn: Tree.Node
  for +seen: Bool
  {Thunk.lams(nn, seen) == Laws.thunk.args(nn, seen) : Nat}

def thunk.lams(nn, seen):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{+k, +t, l, c}:
              +s2 = Bool.and(Bool.not(Lex.is_comma(k)), Bool.or(seen, String.eq(t, "=>")))
              +p = Bool.pick(Nat, Bool.and(Lex.is_comma(k), seen), 1n, 0n)
              Equal.cong(Nat, Nat, x => Nat.add(p, x), Thunk.lams(rest, s2), Laws.thunk.args(rest, s2),
                thunk.lams(rest, s2))
        case Tree.Group{x, y, z}: thunk.lams(rest, seen)
        case Tree.Stmt{x, y, z}: thunk.lams(rest, seen)
        case Tree.NNil{}: thunk.lams(rest, seen)
        case Tree.NCons{x, y}: thunk.lams(rest, seen)
    case Tree.Leaf{x}: {==}
    case Tree.Group{x, y, z}: {==}
    case Tree.Stmt{x, y, z}: {==}
    case Tree.NNil{}: {==}

# the rule's call given one lambda is the law's
law thunk.only:
  for +o: String
  for +kids: Tree.Node
  {Thunk.only(o, kids) == Laws.thunk.lone(o, kids) : Bool}

def thunk.only(o, kids):
  Equal.cong(Nat, Bool, x => Bool.and(String.eq(o, "("), Nat.is_eq(x, 1n)), Thunk.lams(kids, False{}),
    Laws.thunk.args(kids, False{}), thunk.lams(kids, False{}))

# a site gated by lone: the rule's finding is the law's count
law thunk.gate:
  for +lone: Bool
  for hh: Tree.Node
  for rest: Tree.Node
  for +name: String
  for +path: String
  {List.length(&2, F.Finding, Bool.pick(List<&2, F.Finding>, lone, Thunk.site(hh, rest, name, path), []))
    == Bool.pick(Nat, Bool.and(lone, Laws.thunk.at(Tree.NCons{hh, rest}, name)), 1n, 0n) : Nat}

def thunk.gate(lone, hh, rest, name, path):
  match lone:
    case True{}: thunk.site(hh, rest, name, path)
    case False{}: {==}

def Laws.thunk_walk_counts(nn, lone, name, path):
  match nn:
    case Tree.NCons{+h, +rest}:
      M1.table.three(Bool.pick(List<&2, F.Finding>, lone, Thunk.site(h, rest, name, path), []),
        Thunk.walk(h, False{}, name, path), Thunk.walk(rest, lone, name, path),
        Bool.pick(Nat, Bool.and(lone, Laws.thunk.at(Tree.NCons{h, rest}, name)), 1n, 0n),
        Laws.thunk.count(h, False{}, name), Laws.thunk.count(rest, lone, name), thunk.gate(lone, h, rest, name, path),
        Laws.thunk_walk_counts(h, False{}, name, path), Laws.thunk_walk_counts(rest, lone, name, path))
    case Tree.Group{open, +kids, cl}:
      match open:
        case Lex.Tok{k, +o, l, c}:
          %thunk.only(o, kids) : {List.length(&2, F.Finding, Thunk.walk(kids, Thunk.only(o, kids), name, path))
            == Laws.thunk.count(kids, _, name) : Nat}
          Laws.thunk_walk_counts(kids, Thunk.only(o, kids), name, path)
    case Tree.Stmt{sk, +kids, +body}:
      M1.table.two(Thunk.walk(kids, False{}, name, path), Thunk.walk(body, False{}, name, path),
        Laws.thunk.count(kids, False{}, name), Laws.thunk.count(body, False{}, name),
        Laws.thunk_walk_counts(kids, False{}, name, path), Laws.thunk_walk_counts(body, False{}, name, path))
    case Tree.Leaf{tok}:
      {==}
    case Tree.NNil{}:
      {==}

# one def's findings: none when it is exempt, else its walk
law thunk.stop:
  for b: Bool
  for +body: Tree.Node
  for +name: String
  for +path: String
  {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, b, [], _u => Thunk.walk(body, False{}, name, path)))
    == Bool.pick(Nat, b, 0n, Laws.thunk.count(body, False{}, name)) : Nat}

def thunk.stop(b, body, name, path):
  match b:
    case True{}:
      {==}
    case False{}:
      Laws.thunk_walk_counts(body, False{}, name, path)

# thunk's def walk: the findings gathered so far, then each def's
law thunk.go:
  for ds: List<&2, Calls.Def>
  for +path: String
  for +acc: List<&2, List<&2, F.Finding>>
  {List.length(&2, F.Finding, Thunk.check.go(ds, path, acc)) == M1.pick.sum(acc, Laws.thunk.defs(ds, path)) : Nat}

def thunk.go(ds, path, acc):
  match ds:
    case Nil{}:
      M1.pick.rev(acc, Nil{})
    case Con{d, +rest}:
      match d:
        case Calls.Def{+name, +sig, +body}:
          +b = Calls.exempt(path, sig)
          +x = Lazy.stop(List<&2, F.Finding>, b, [], _u => Thunk.walk(body, False{}, name, path))
          +cb = Bool.pick(Nat, b, 0n, Laws.thunk.count(body, False{}, name))
          Equal.trans(Nat, List.length(&2, F.Finding, Thunk.check.go(rest, path, x <> acc)),
            M1.pick.sum(acc, Nat.add(List.length(&2, F.Finding, x), Laws.thunk.defs(rest, path))),
            M1.pick.sum(acc, Nat.add(cb, Laws.thunk.defs(rest, path))),
            thunk.go(rest, path, x <> acc),
            Equal.cong(Nat, Nat, n => M1.pick.sum(acc, Nat.add(n, Laws.thunk.defs(rest, path))),
              List.length(&2, F.Finding, x), cb, thunk.stop(b, body, name, path)))

def Laws.thunk_counts(path, _text, _toks, tree, _bound, _items):
  thunk.go(Calls.defs(tree), path, Nil{})
