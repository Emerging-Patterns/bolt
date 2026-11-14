# proofs of laws/PickReportsSelfCalls.bend
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/lazy/lazy.bend as Lazy
import ../src/syntax/tree.bend as Tree
import ../src/rules/calls.bend as Calls
import ../src/rules/correctness/pick.bend as Pick
import ../laws/PickReportsSelfCalls.bend as Laws
import ./lemmas/Pick.bend as M1

# either finding of a pick is the law's hit: a branch calls the def
law pick.either:
  for p: Bool
  for q: Bool
  for a: Bool
  for b: Bool
  {Bool.or(Bool.and(Bool.and(p, Bool.not(q)), Bool.and(a, b)),
      Bool.and(Bool.and(p, Bool.not(Bool.and(Bool.and(p, Bool.not(q)), Bool.and(a, b)))),
        Bool.and(Bool.not(q), Bool.or(a, b))))
    == Bool.and(p, Bool.and(Bool.not(q), Bool.or(a, b))) : Bool}

def pick.either(p, q, a, b):
  match p q a b:
    case False{} q a b:
      {==}
    case True{} True{} a b:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case True{} False{} False{} b:
      {==}

# quiet or'd with a hush that does not apply is quiet
law pick.off:
  for q: Bool
  for h: Bool
  {q == Bool.or(q, Bool.and(h, False{})) : Bool}

def pick.off(q, h):
  match q h:
    case True{} h:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# quiet or'd with a hush that applies is the plain or
law pick.on:
  for q: Bool
  for h: Bool
  {Bool.or(q, h) == Bool.or(q, Bool.and(h, True{})) : Bool}

def pick.on(q, h):
  match q h:
    case True{} h:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def Laws.pick_mute(q, h, n):
  match n:
    case 0n:
      pick.off(q, h)
    case 1n:
      pick.off(q, h)
    case 2n:
      pick.on(q, h)
    case 3n:
      pick.on(q, h)
    case 4n+p:
      pick.off(q, h)

def Laws.pick_next(k, _n):
  match k:
    case Lex.TName{}:
      {==}
    case Lex.TUpper{}:
      {==}
    case Lex.TDotted{}:
      {==}
    case Lex.TWild{}:
      {==}
    case Lex.TKey{}:
      {==}
    case Lex.TNum{}:
      {==}
    case Lex.TStr{}:
      {==}
    case Lex.TChar{}:
      {==}
    case Lex.TComment{}:
      {==}
    case Lex.TSpace{}:
      {==}
    case Lex.TNewline{}:
      {==}
    case Lex.TOp{}:
      {==}
    case Lex.TColon{}:
      {==}
    case Lex.TEq{}:
      {==}
    case Lex.TBind{}:
      {==}
    case Lex.TArrow{}:
      {==}
    case Lex.TLam{}:
      {==}
    case Lex.TAll{}:
      {==}
    case Lex.TAmp{}:
      {==}
    case Lex.TOpen{}:
      {==}
    case Lex.TClose{}:
      {==}
    case Lex.TComma{}:
      {==}

# the walk in a state the law's count reaches another way
law pick.move:
  for +n: Tree.Node
  for +name: String
  for +path: String
  for +q1: Bool
  for +q2: Bool
  for +h1: Bool
  for +h2: Bool
  for +n1: Nat
  for +n2: Nat
  for eq: {q1 == q2 : Bool}
  for eh: {h1 == h2 : Bool}
  for en: {n1 == n2 : Nat}
  for ih: {List.length(&2, F.Finding, Pick.walk(n, name, path, q1, h1, n1))
    == Laws.pick.count(n, name, q1, h1, n1) : Nat}
  {List.length(&2, F.Finding, Pick.walk(n, name, path, q1, h1, n1)) == Laws.pick.count(n, name, q2, h2, n2) : Nat}

def pick.move(n, name, path, q1, q2, h1, h2, n1, n2, eq, eh, en, ih):
  Equal.trans(Nat, List.length(&2, F.Finding, Pick.walk(n, name, path, q1, h1, n1)),
    Laws.pick.count(n, name, q1, h1, n1), Laws.pick.count(n, name, q2, h2, n2), ih,
    Equal.trans(Nat, Laws.pick.count(n, name, q1, h1, n1), Laws.pick.count(n, name, q2, h1, n1),
      Laws.pick.count(n, name, q2, h2, n2), Equal.cong(Bool, Nat, x => Laws.pick.count(n, name, x, h1, n1), q1, q2,
        eq),
      Equal.trans(Nat, Laws.pick.count(n, name, q2, h1, n1), Laws.pick.count(n, name, q2, h2, n1),
        Laws.pick.count(n, name, q2, h2, n2), Equal.cong(Bool, Nat, x => Laws.pick.count(n, name, q2, x, n1), h1, h2,
          eh),
        Equal.cong(Nat, Nat, x => Laws.pick.count(n, name, q2, h2, x), n1, n2, en))))

# the law's count at a pick call, the call being argument at with quiet q
def pick.at(
  +t: String,
  +kids: Tree.Node,
  +rest: Tree.Node,
  +name: String,
  +quiet: Bool,
  +hush: Bool,
  +at: Nat,
  +q: Bool
) -> Nat:
  +hit = Bool.and(String.eq(t, "Bool.pick"), Bool.and(Bool.not(q), Laws.pick.branch(Calls.args(kids), name)))
  +m = Nat.add(Laws.pick.count(kids, name, q, hit, 0n), Laws.pick.count(rest, name, quiet, hush, at))
  Bool.pick(Nat, hit, 1n+m, m)

# a finding for both branches, else one for one branch, adds one to the count
# exactly when a branch calls the def
law pick.hit:
  for p: Bool
  for q: Bool
  for a: Bool
  for b: Bool
  for -x: F.Finding
  for -y: F.Finding
  for -more: List<&2, F.Finding>
  for -m: Nat
  for ih: {List.length(&2, F.Finding, more) == m : Nat}
  {List.length(&2, F.Finding,
      Bool.pick(List<&2, F.Finding>, Bool.and(Bool.and(p, Bool.not(q)), Bool.and(a, b)), x <> more,
        Bool.pick(List<&2, F.Finding>,
          Bool.and(Bool.and(p, Bool.not(Bool.and(Bool.and(p, Bool.not(q)), Bool.and(a, b)))),
            Bool.and(Bool.not(q), Bool.or(a, b))), y <> more, more)))
    == Bool.pick(Nat, Bool.and(p, Bool.and(Bool.not(q), Bool.or(a, b))), 1n+m, m) : Nat}

def pick.hit(p, q, a, b, _x, _y, more, m, ih):
  match p q a b:
    case False{} q a b:
      ih
    case True{} True{} a b:
      ih
    case True{} False{} True{} True{}:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, F.Finding, more), m, ih)
    case True{} False{} True{} False{}:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, F.Finding, more), m, ih)
    case True{} False{} False{} True{}:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, F.Finding, more), m, ih)
    case True{} False{} False{} False{}:
      ih

def Laws.pick_walk_counts(nn, name, path, quiet, hush, nth):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{+k, +t, +l, +c}:
              match rest:
                case Tree.NCons{h2, +r2}:
                  match h2:
                    case Tree.Group{open, +kids, close}:
                      +at = Pick.next(k, nth)
                      +q = Pick.mute(quiet, hush, at)
                      +as = Calls.args(kids)
                      +p = String.eq(t, "Bool.pick")
                      +a = Calls.calls(Calls.arg(as, 2n), name)
                      +b = Calls.calls(Calls.arg(as, 3n), name)
                      +two = Bool.and(Bool.and(p, Bool.not(q)), Bool.and(a, b))
                      +one = Bool.and(Bool.and(p, Bool.not(two)), Bool.and(Bool.not(q), Bool.or(a, b)))
                      +hit = Bool.and(p, Bool.and(Bool.not(q), Bool.or(a, b)))
                      +fk = Pick.walk(kids, name, path, q, Bool.or(two, one), 0n)
                      +fr = Pick.walk(r2, name, path, quiet, hush, at)
                      +ck = Laws.pick.count(kids, name, q, hit, 0n)
                      +cr = Laws.pick.count(r2, name, quiet, hush, at)
                      +found = pick.hit(p, q, a, b,
                        F.Finding{path, l, c, 9, "pick",
                          name ++ " calls itself in both branches of Bool.pick, which evaluates both, so both calls run; bind the call once above the pick."},
                        F.Finding{path, l, c, 9, "pick",
                          name ++ " calls itself in one branch of Bool.pick, which evaluates both, so the call always runs and never exits early; branch with `match` on the condition instead."},
                        List.concat(&2, F.Finding, [fk, fr]), Nat.add(ck, cr),
                        M1.pick.join(fk, List.append(&2, F.Finding, fr, Nil{}), ck, cr,
                          pick.move(kids, name, path, q, q, Bool.or(two, one), hit, 0n, 0n, {==}, pick.either(p, q, a,
                            b), {==},
                            Laws.pick_walk_counts(kids, name, path, q, Bool.or(two, one), 0n)),
                          M1.pick.last(fr, cr, Laws.pick_walk_counts(r2, name, path, quiet, hush, at))))
                      Equal.trans(Nat, List.length(&2, F.Finding, Pick.walk(Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}},
                        rest}, name, path, quiet, hush, nth)), pick.at(t, kids, r2, name, quiet, hush, at, q),
                        pick.at(t, kids, r2, name, quiet, hush, Laws.pick.step(k, nth), Laws.pick.hushed(quiet, hush,
                          Laws.pick.step(k, nth))), found,
                        Equal.trans(Nat, pick.at(t, kids, r2, name, quiet, hush, at, q), pick.at(t, kids, r2, name,
                          quiet, hush, at, Laws.pick.hushed(quiet, hush, at)),
                          pick.at(t, kids, r2, name, quiet, hush, Laws.pick.step(k, nth), Laws.pick.hushed(quiet, hush,
                            Laws.pick.step(k, nth))),
                          Equal.cong(Bool, Nat, x => pick.at(t, kids, r2, name, quiet, hush, at, x), q,
                            Laws.pick.hushed(quiet, hush, at),
                            Laws.pick_mute(quiet, hush, at)),
                          Equal.cong(Nat, Nat, x => pick.at(t, kids, r2, name, quiet, hush, x, Laws.pick.hushed(quiet,
                            hush, x)), at, Laws.pick.step(k, nth),
                            Laws.pick_next(k, nth))))
                    case Tree.Leaf{x}:
                      pick.move(rest, name, path, quiet, quiet, hush, hush, Pick.next(k, nth), Laws.pick.step(k, nth),
                        {==}, {==},
                        Laws.pick_next(k, nth), Laws.pick_walk_counts(rest, name, path, quiet, hush, Pick.next(k, nth)))
                    case Tree.Stmt{kind, kids, body}:
                      pick.move(rest, name, path, quiet, quiet, hush, hush, Pick.next(k, nth), Laws.pick.step(k, nth),
                        {==}, {==},
                        Laws.pick_next(k, nth), Laws.pick_walk_counts(rest, name, path, quiet, hush, Pick.next(k, nth)))
                    case Tree.NNil{}:
                      pick.move(rest, name, path, quiet, quiet, hush, hush, Pick.next(k, nth), Laws.pick.step(k, nth),
                        {==}, {==},
                        Laws.pick_next(k, nth), Laws.pick_walk_counts(rest, name, path, quiet, hush, Pick.next(k, nth)))
                    case Tree.NCons{x, y}:
                      pick.move(rest, name, path, quiet, quiet, hush, hush, Pick.next(k, nth), Laws.pick.step(k, nth),
                        {==}, {==},
                        Laws.pick_next(k, nth), Laws.pick_walk_counts(rest, name, path, quiet, hush, Pick.next(k, nth)))
                case Tree.Leaf{x}:
                  pick.move(rest, name, path, quiet, quiet, hush, hush, Pick.next(k, nth), Laws.pick.step(k, nth), {==},
                    {==},
                    Laws.pick_next(k, nth), Laws.pick_walk_counts(rest, name, path, quiet, hush, Pick.next(k, nth)))
                case Tree.Group{open, kids, close}:
                  pick.move(rest, name, path, quiet, quiet, hush, hush, Pick.next(k, nth), Laws.pick.step(k, nth), {==},
                    {==},
                    Laws.pick_next(k, nth), Laws.pick_walk_counts(rest, name, path, quiet, hush, Pick.next(k, nth)))
                case Tree.Stmt{kind, kids, body}:
                  pick.move(rest, name, path, quiet, quiet, hush, hush, Pick.next(k, nth), Laws.pick.step(k, nth), {==},
                    {==},
                    Laws.pick_next(k, nth), Laws.pick_walk_counts(rest, name, path, quiet, hush, Pick.next(k, nth)))
                case Tree.NNil{}:
                  pick.move(rest, name, path, quiet, quiet, hush, hush, Pick.next(k, nth), Laws.pick.step(k, nth), {==},
                    {==},
                    Laws.pick_next(k, nth), Laws.pick_walk_counts(rest, name, path, quiet, hush, Pick.next(k, nth)))
        case Tree.Group{open, +kids, close}:
          +fr = Pick.walk(rest, name, path, quiet, hush, nth)
          +cr = Laws.pick.count(rest, name, quiet, hush, nth)
          M1.pick.join(Pick.walk(kids, name, path, Pick.mute(quiet, hush, nth), False{}, 0n), List.append(&2, F.Finding,
            fr, Nil{}),
            Laws.pick.count(kids, name, Laws.pick.hushed(quiet, hush, nth), False{}, 0n), cr,
            pick.move(kids, name, path, Pick.mute(quiet, hush, nth), Laws.pick.hushed(quiet, hush, nth), False{},
              False{}, 0n, 0n, Laws.pick_mute(quiet, hush, nth), {==}, {==},
              Laws.pick_walk_counts(kids, name, path, Pick.mute(quiet, hush, nth), False{}, 0n)),
            M1.pick.last(fr, cr, Laws.pick_walk_counts(rest, name, path, quiet, hush, nth)))
        case Tree.Stmt{kind, +kids, +body}:
          +fb = Pick.walk(body, name, path, Pick.mute(quiet, hush, nth), False{}, 0n)
          +fr = Pick.walk(rest, name, path, quiet, hush, nth)
          +cb = Laws.pick.count(body, name, Laws.pick.hushed(quiet, hush, nth), False{}, 0n)
          +cr = Laws.pick.count(rest, name, quiet, hush, nth)
          M1.pick.join(Pick.walk(kids, name, path, Pick.mute(quiet, hush, nth), False{}, 0n),
            List.append(&2, F.Finding, fb, List.append(&2, F.Finding, fr, Nil{})),
            Laws.pick.count(kids, name, Laws.pick.hushed(quiet, hush, nth), False{}, 0n), Nat.add(cb, cr),
            pick.move(kids, name, path, Pick.mute(quiet, hush, nth), Laws.pick.hushed(quiet, hush, nth), False{},
              False{}, 0n, 0n, Laws.pick_mute(quiet, hush, nth), {==}, {==},
              Laws.pick_walk_counts(kids, name, path, Pick.mute(quiet, hush, nth), False{}, 0n)),
            M1.pick.join(fb, List.append(&2, F.Finding, fr, Nil{}), cb, cr,
              pick.move(body, name, path, Pick.mute(quiet, hush, nth), Laws.pick.hushed(quiet, hush, nth), False{},
                False{}, 0n, 0n, Laws.pick_mute(quiet, hush, nth), {==}, {==},
              Laws.pick_walk_counts(body, name, path, Pick.mute(quiet, hush, nth), False{}, 0n)),
              M1.pick.last(fr, cr, Laws.pick_walk_counts(rest, name, path, quiet, hush, nth))))
        case Tree.NNil{}:
          Laws.pick_walk_counts(rest, name, path, quiet, hush, nth)
        case Tree.NCons{x, y}:
          Laws.pick_walk_counts(rest, name, path, quiet, hush, nth)
    case Tree.Leaf{tok}:
      {==}
    case Tree.Group{open, kids, close}:
      {==}
    case Tree.Stmt{kind, kids, body}:
      {==}
    case Tree.NNil{}:
      {==}

def Laws.pick_picks_counts(nn, name, path, quiet):
  Laws.pick_walk_counts(nn, name, path, quiet, False{}, 0n)

# one def's findings, exempt or walked
law pick.stop:
  for b: Bool
  for +body: Tree.Node
  for +name: String
  for +path: String
  {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, b, [], _u => Pick.picks(body, name, path, False{})))
    == Bool.pick(Nat, b, 0n, Laws.pick.count(body, name, False{}, False{}, 0n)) : Nat}

def pick.stop(b, body, name, path):
  match b:
    case True{}:
      {==}
    case False{}:
      Laws.pick_walk_counts(body, name, path, False{}, False{}, 0n)

# pick's def walk: the findings gathered so far, then each def's
law pick.go:
  for ds: List<&2, Calls.Def>
  for +path: String
  for +acc: List<&2, List<&2, F.Finding>>
  {List.length(&2, F.Finding, Pick.check.go(ds, path, acc)) == M1.pick.sum(acc, Laws.pick.defs(ds, path)) : Nat}

def pick.go(ds, path, acc):
  match ds:
    case Nil{}:
      M1.pick.rev(acc, Nil{})
    case Con{Calls.Def{+name, +sig, +body}, +rest}:
      +x = Lazy.stop(List<&2, F.Finding>, Calls.exempt(path, sig), [], _u => Pick.picks(body, name, path, False{}))
      Equal.trans(Nat, List.length(&2, F.Finding, Pick.check.go(rest, path, x <> acc)),
        M1.pick.sum(acc, Nat.add(List.length(&2, F.Finding, x), Laws.pick.defs(rest, path))),
        M1.pick.sum(acc, Nat.add(Bool.pick(Nat, Calls.exempt(path, sig), 0n, Laws.pick.count(body, name, False{},
            False{},
          0n)),
          Laws.pick.defs(rest, path))),
        pick.go(rest, path, x <> acc),
        Equal.cong(Nat, Nat, n => M1.pick.sum(acc, Nat.add(n, Laws.pick.defs(rest, path))),
          List.length(&2, F.Finding, x), Bool.pick(Nat, Calls.exempt(path, sig), 0n, Laws.pick.count(body, name,
            False{}, False{}, 0n)),
          pick.stop(Calls.exempt(path, sig), body, name, path)))

def Laws.pick_counts(path, _text, _toks, tree, _bound, _items):
  pick.go(Calls.defs(tree), path, Nil{})
