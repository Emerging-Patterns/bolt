# proofs of laws/RingReportsDropAppendRotation.bend
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/lazy/lazy.bend as Lazy
import ../src/syntax/tree.bend as Tree
import ../src/rules/calls.bend as Calls
import ../src/rules/correctness/pick.bend as Pick
import ../src/rules/suspicious/ring.bend as Ring
import ../laws/RingReportsDropAppendRotation.bend as Laws
import ./lemmas/Pick.bend as M1

# a scan's finding counts one when it found a drop, else none
law ring.one:
  for mm: Maybe<&2, Lex.Tok>
  for +path: String
  {List.length(&2, F.Finding, Ring.slide_at(mm, path)) == Laws.ring.hit(mm) : Nat}

def ring.one(mm, _path):
  match mm:
    case None{}:
      {==}
    case Some{Lex.Tok{k, t, l, c}}:
      {==}

# a self-call's arguments, each read against its own slot
law ring.slides:
  for as: List<&2, Tree.Node>
  for +params: List<&2, String>
  for +path: String
  for +wins: List<&2, String>
  {List.length(&2, F.Finding, Ring.slides(as, params, path, wins)) == Laws.ring.args(as, params, wins) : Nat}

def ring.slides(as, params, path, wins):
  match as:
    case Nil{}:
      {==}
    case Con{+h, +rest}:
      +scan = Ring.plus_scan(h, None{}, Ring.slot_wins(Maybe.default(&2, String, List.head(&2, String, params), ""),
        wins))
      +x = Ring.slide_at(scan, path)
      +more = Ring.slides(rest, List.tail(&2, String, params), path, wins)
      Equal.trans(Nat, List.length(&2, F.Finding, List.append(&2, F.Finding, x, more)),
        Nat.add(List.length(&2, F.Finding, x), List.length(&2, F.Finding, more)),
        Nat.add(Laws.ring.hit(scan), Laws.ring.args(rest, List.tail(&2, String, params), wins)),
        M1.esc.app(x, more),
        M1.esc.add(List.length(&2, F.Finding, x), Laws.ring.hit(scan), List.length(&2, F.Finding, more),
          Laws.ring.args(rest, List.tail(&2, String, params), wins), ring.one(scan, path),
          ring.slides(rest, List.tail(&2, String, params), path, wins)))

def Laws.ring_walk_counts(nn, self, params, path, wins):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{Lex.Tok{k, +t, l, c}}:
          match rest:
            case Tree.NCons{h2, +r2}:
              match h2:
                case Tree.Group{Lex.Tok{k2, +o, l2, c2}, +kids, cl}:
                  +me = Bool.and(String.eq(o, "("), String.eq(t, self))
                  M1.table.three(
                    Lazy.stop(List<&2, F.Finding>, Bool.not(me), [], _u => Ring.slides(Calls.args(kids), params, path,
                      wins)),
                    Ring.walk(kids, self, params, path, wins), Ring.walk(r2, self, params, path, wins),
                    Bool.pick(Nat, me, Laws.ring.args(Calls.args(kids), params, wins), 0n),
                    Laws.ring.count(kids, self, params, wins), Laws.ring.count(r2, self, params, wins),
                    M1.tail.stop(me, Ring.slides(Calls.args(kids), params, path, wins),
                      Laws.ring.args(Calls.args(kids), params, wins),
                      ring.slides(Calls.args(kids), params, path, wins)),
                    Laws.ring_walk_counts(kids, self, params, path, wins),
                    Laws.ring_walk_counts(r2, self, params, path, wins))
                case Tree.Leaf{x}:
                  Laws.ring_walk_counts(rest, self, params, path, wins)
                case Tree.Stmt{a, b, d}:
                  Laws.ring_walk_counts(rest, self, params, path, wins)
                case Tree.NNil{}:
                  Laws.ring_walk_counts(rest, self, params, path, wins)
                case Tree.NCons{a, b}:
                  Laws.ring_walk_counts(rest, self, params, path, wins)
            case Tree.Leaf{x}:
              Laws.ring_walk_counts(rest, self, params, path, wins)
            case Tree.Group{a, b, d}:
              Laws.ring_walk_counts(rest, self, params, path, wins)
            case Tree.Stmt{a, b, d}:
              Laws.ring_walk_counts(rest, self, params, path, wins)
            case Tree.NNil{}:
              Laws.ring_walk_counts(rest, self, params, path, wins)
        case Tree.Group{open, +kids, close}:
          M1.table.two(Ring.walk(kids, self, params, path, wins), Ring.walk(rest, self, params, path, wins),
            Laws.ring.count(kids, self, params, wins), Laws.ring.count(rest, self, params, wins),
            Laws.ring_walk_counts(kids, self, params, path, wins),
            Laws.ring_walk_counts(rest, self, params, path, wins))
        case Tree.Stmt{kind, +kids, +body}:
          M1.table.three(Ring.walk(kids, self, params, path, wins), Ring.walk(body, self, params, path, wins),
            Ring.walk(rest, self, params, path, wins), Laws.ring.count(kids, self, params, wins),
            Laws.ring.count(body, self, params, wins), Laws.ring.count(rest, self, params, wins),
            Laws.ring_walk_counts(kids, self, params, path, wins),
            Laws.ring_walk_counts(body, self, params, path, wins),
            Laws.ring_walk_counts(rest, self, params, path, wins))
        case Tree.NNil{}:
          Laws.ring_walk_counts(rest, self, params, path, wins)
        case Tree.NCons{a, b}:
          Laws.ring_walk_counts(rest, self, params, path, wins)
    case Tree.Leaf{x}:
      {==}
    case Tree.Group{a, b, d}:
      {==}
    case Tree.Stmt{a, b, d}:
      {==}
    case Tree.NNil{}:
      {==}

# one def's findings: walked when its guard keeps it, else none
law ring.stop:
  for +b: Bool
  for +body: Tree.Node
  for +self: String
  for +params: List<&2, String>
  for +path: String
  for +wins: List<&2, String>
  {List.length(&2, F.Finding,
    Lazy.stop(List<&2, F.Finding>, Bool.not(b), [], _u => Ring.walk(body, self, params, path, wins)))
    == Bool.pick(Nat, b, Laws.ring.count(body, self, params, wins), 0n) : Nat}

def ring.stop(b, body, self, params, path, wins):
  match b:
    case True{}:
      Laws.ring_walk_counts(body, self, params, path, wins)
    case False{}:
      {==}

# ring's def walk: the findings gathered so far, then each def's
law ring.go:
  for ds: List<&2, Calls.Def>
  for +path: String
  for +acc: List<&2, List<&2, F.Finding>>
  {List.length(&2, F.Finding, Ring.check.go(ds, path, acc)) == M1.pick.sum(acc, Laws.ring.defs(ds, path)) : Nat}

def ring.go(ds, path, acc):
  match ds:
    case Nil{}:
      M1.pick.rev(acc, Nil{})
    case Con{Calls.Def{+name, +sig, +body}, +rest}:
      +keep = Bool.and(Calls.calls(body, name), Bool.not(Calls.exempt(path, sig)))
      +x = Lazy.stop(List<&2, F.Finding>, Bool.not(keep), [],
        _u => Ring.walk(body, name, Calls.names(sig), path, Ring.windows(sig, body)))
      +cb = Bool.pick(Nat, keep, Laws.ring.count(body, name, Calls.names(sig), Ring.windows(sig, body)), 0n)
      Equal.trans(Nat, List.length(&2, F.Finding, Ring.check.go(rest, path, x <> acc)),
        M1.pick.sum(acc, Nat.add(List.length(&2, F.Finding, x), Laws.ring.defs(rest, path))),
        M1.pick.sum(acc, Nat.add(cb, Laws.ring.defs(rest, path))),
        ring.go(rest, path, x <> acc),
        Equal.cong(Nat, Nat, n => M1.pick.sum(acc, Nat.add(n, Laws.ring.defs(rest, path))),
          List.length(&2, F.Finding, x), cb,
          ring.stop(keep, body, name, Calls.names(sig), path, Ring.windows(sig, body))))

def Laws.ring_counts(path, _text, _toks, tree, _bound, _items):
  ring.go(Calls.defs(tree), path, Nil{})
