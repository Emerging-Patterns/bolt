# proofs of laws/HoistReportsTablesInLoops.bend
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/lazy/lazy.bend as Lazy
import ../src/syntax/tree.bend as Tree
import ../src/rules/calls.bend as Calls
import ../src/rules/correctness/pick.bend as Pick
import ../src/rules/suspicious/hoist.bend as Hoist
import ../laws/HoistReportsTablesInLoops.bend as Laws
import ./lemmas/MatchStatementCounts.bend as M1
import ./lemmas/Pick.bend as M2

# The recursion rule, hoist: each call adds the one the law's call test
# counts, each plain let the one its let test counts, the heat follows the
# same lambdas and case arms, and the def walk joins the per-def lists into
# their sum.

# a table found or not: one finding or none
law hoist.yes:
  for b: Bool
  for -aa: Tree.Node
  for -path: String
  {List.length(&2, F.Finding, Hoist.one_yes(b, aa, path)) == Bool.pick(Nat, b, 1n, 0n) : Nat}

def hoist.yes(b, _aa, _path):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# a get or set's collection: one finding when the law's slot test holds
law hoist.slot:
  for ss: Hoist.Slot
  for +as: List<&2, Tree.Node>
  for +self: String
  for +wides: List<&2, String>
  for +carried: List<&2, String>
  for +path: String
  {List.length(&2, F.Finding, Hoist.arg_table(ss, as, self, wides, carried, path))
    == Bool.pick(Nat, Laws.hoist.slot(ss, as, self, wides, carried), 1n, 0n) : Nat}

def hoist.slot(ss, as, self, wides, carried, path):
  match ss:
    case Hoist.Slot{on, at}:
      match on:
        case False{}:
          {==}
        case True{}:
          hoist.yes(Hoist.is_table(Calls.arg(as, at), self, wides, carried), Calls.arg(as, at), path)

# a call site: one finding when the law's call test holds
law hoist.call:
  for hot: Bool
  for open: Bool
  for +tt: String
  for +kids: Tree.Node
  for +self: String
  for +wides: List<&2, String>
  for +carried: List<&2, String>
  for +path: String
  {List.length(&2, F.Finding, Hoist.call_table(hot, open, tt, kids, self, wides, carried, path))
    == Bool.pick(Nat, Laws.hoist.call(hot, open, tt, kids, self, wides, carried), 1n, 0n) : Nat}

def hoist.call(hot, open, tt, kids, self, wides, carried, path):
  match hot:
    case False{}:
      {==}
    case True{}:
      match open:
        case False{}:
          {==}
        case True{}:
          hoist.slot(Hoist.slot_of(tt), Calls.args(kids), self, wides, carried, path)

# a let's table and use: one finding when both hold
law hoist.use:
  for a: Bool
  for b: Bool
  for -expr: Tree.Node
  for -path: String
  {List.length(&2, F.Finding, Hoist.let_use(a, b, expr, path)) == Bool.pick(Nat, Bool.and(a, b), 1n, 0n) : Nat}

def hoist.use(a, b, _expr, _path):
  match a:
    case False{}:
      {==}
    case True{}:
      match b:
        case True{}:
          {==}
        case False{}:
          {==}

# a let's left side read: one finding when the law's got test holds
law hoist.got:
  for mm: Maybe<&2, Hoist.Got>
  for +body: Tree.Node
  for +rest: Tree.Node
  for +self: String
  for +wides: List<&2, String>
  for +carried: List<&2, String>
  for +path: String
  {List.length(&2, F.Finding, Hoist.let_of(mm, body, rest, self, wides, carried, path))
    == Bool.pick(Nat, Laws.hoist.got(mm, body, rest, self, wides, carried), 1n, 0n) : Nat}

def hoist.got(mm, body, rest, self, wides, carried, path):
  match mm:
    case None{}:
      {==}
    case Some{Hoist.Got{+nm, +expr}}:
      hoist.use(Hoist.is_table(expr, self, wides, carried), Hoist.uses_or(body, rest, nm), expr, path)

# a statement: one finding when the law's let test holds
law hoist.let:
  for hot: Bool
  for +kids: Tree.Node
  for +body: Tree.Node
  for +rest: Tree.Node
  for +self: String
  for +wides: List<&2, String>
  for +carried: List<&2, String>
  for +path: String
  {List.length(&2, F.Finding, Hoist.let_hit(hot, kids, body, rest, self, wides, carried, path))
    == Bool.pick(Nat, Laws.hoist.let(hot, kids, body, rest, self, wides, carried), 1n, 0n) : Nat}

def hoist.let(hot, kids, body, rest, self, wides, carried, path):
  match hot:
    case False{}:
      {==}
    case True{}:
      hoist.got(Hoist.eat(kids, False{}, False{}, ""), body, rest, self, wides, carried, path)

# a list joined before another counts as its own count plus the other's
law hoist.front:
  for +a: List<&2, F.Finding>
  for +b: List<&2, F.Finding>
  for -x: Nat
  for -y: Nat
  for e1: {List.length(&2, F.Finding, a) == x : Nat}
  for e2: {List.length(&2, F.Finding, b) == y : Nat}
  {List.length(&2, F.Finding, List.append(&2, F.Finding, a, b)) == Nat.add(x, y) : Nat}

def hoist.front(a, b, x, y, e1, e2):
  Equal.trans(Nat, List.length(&2, F.Finding, List.append(&2, F.Finding, a, b)),
    Nat.add(List.length(&2, F.Finding, a), List.length(&2, F.Finding, b)), Nat.add(x, y),
    M2.esc.app(a, b), M2.esc.add(List.length(&2, F.Finding, a), x, List.length(&2, F.Finding, b), y, e1, e2))

# a name token, then a group: its own finding, then its group's and the
# rest's, all at the heat the token leaves
law hoist.site:
  for +k: Lex.TokKind
  for +t: String
  for +o: String
  for +kids: Tree.Node
  for +rr: Tree.Node
  for +self: String
  for +wides: List<&2, String>
  for +carried: List<&2, String>
  for +path: String
  for +hot: Bool
  for ih1: {List.length(&2, F.Finding, Hoist.walk(kids, self, wides, carried, path, Hoist.warm(hot, k)))
    == Laws.hoist.count(kids, self, wides, carried, Hoist.warm(hot, k)) : Nat}
  for ih2: {List.length(&2, F.Finding, Hoist.walk(rr, self, wides, carried, path, Hoist.warm(hot, k)))
    == Laws.hoist.count(rr, self, wides, carried, Hoist.warm(hot, k)) : Nat}
  {List.length(&2, F.Finding, List.concat(&2, F.Finding,
      [Hoist.call_table(Hoist.warm(hot, k), String.eq(o, "("), t, kids, self, wides, carried, path),
        Hoist.walk(kids, self, wides, carried, path, Hoist.warm(hot, k)),
        Hoist.walk(rr, self, wides, carried, path, Hoist.warm(hot, k))]))
    == Nat.add(Bool.pick(Nat, Laws.hoist.call(Hoist.warm(hot, k), String.eq(o, "("), t, kids, self, wides, carried),
      1n, 0n), Nat.add(Laws.hoist.count(kids, self, wides, carried, Hoist.warm(hot, k)),
        Laws.hoist.count(rr, self, wides, carried, Hoist.warm(hot, k)))) : Nat}

def hoist.site(k, t, o, kids, rr, self, wides, carried, path, hot, ih1, ih2):
  +heat = Hoist.warm(hot, k)
  M1.chars.sum(Hoist.call_table(heat, String.eq(o, "("), t, kids, self, wides, carried, path),
    Hoist.walk(kids, self, wides, carried, path, heat), Hoist.walk(rr, self, wides, carried, path, heat),
    Bool.pick(Nat, Laws.hoist.call(heat, String.eq(o, "("), t, kids, self, wides, carried), 1n, 0n),
    Laws.hoist.count(kids, self, wides, carried, heat), Laws.hoist.count(rr, self, wides, carried, heat),
    hoist.call(heat, String.eq(o, "("), t, kids, self, wides, carried, path), ih1, ih2)

# a case: its pattern cold, its arm hot when it calls the def, then the rest
law hoist.arm:
  for +kids: Tree.Node
  for +body: Tree.Node
  for +rest: Tree.Node
  for +self: String
  for +wides: List<&2, String>
  for +carried: List<&2, String>
  for +path: String
  for +hot: Bool
  for ih1: {List.length(&2, F.Finding, Hoist.walk(kids, self, wides, carried, path, False{}))
    == Laws.hoist.count(kids, self, wides, carried, False{}) : Nat}
  for ih2: {List.length(&2, F.Finding,
      Hoist.walk(body, self, wides, carried, path, Bool.and(hot, Calls.calls(body, self))))
    == Laws.hoist.count(body, self, wides, carried, Bool.and(hot, Calls.calls(body, self))) : Nat}
  for ih3: {List.length(&2, F.Finding, Hoist.walk(rest, self, wides, carried, path, hot))
    == Laws.hoist.count(rest, self, wides, carried, hot) : Nat}
  {List.length(&2, F.Finding, Hoist.walk(Tree.NCons{Tree.Stmt{Tree.SCase{}, kids, body}, rest},
      self, wides, carried, path, hot))
    == Laws.hoist.count(Tree.NCons{Tree.Stmt{Tree.SCase{}, kids, body}, rest}, self, wides, carried, hot) : Nat}

def hoist.arm(kids, body, rest, self, wides, carried, path, hot, ih1, ih2, ih3):
  +arm = Bool.and(hot, Calls.calls(body, self))
  M1.chars.sum(Hoist.walk(kids, self, wides, carried, path, False{}), Hoist.walk(body, self, wides, carried, path, arm),
    Hoist.walk(rest, self, wides, carried, path, hot),
    Laws.hoist.count(kids, self, wides, carried, False{}), Laws.hoist.count(body, self, wides, carried, arm),
    Laws.hoist.count(rest, self, wides, carried, hot), ih1, ih2, ih3)

# any other statement: its own let finding, then its tokens', its block's
# and the rest's
law hoist.plain:
  for +kids: Tree.Node
  for +body: Tree.Node
  for +rest: Tree.Node
  for +self: String
  for +wides: List<&2, String>
  for +carried: List<&2, String>
  for +path: String
  for +hot: Bool
  for ih1: {List.length(&2, F.Finding, Hoist.walk(kids, self, wides, carried, path, hot))
    == Laws.hoist.count(kids, self, wides, carried, hot) : Nat}
  for ih2: {List.length(&2, F.Finding, Hoist.walk(body, self, wides, carried, path, hot))
    == Laws.hoist.count(body, self, wides, carried, hot) : Nat}
  for ih3: {List.length(&2, F.Finding, Hoist.walk(rest, self, wides, carried, path, hot))
    == Laws.hoist.count(rest, self, wides, carried, hot) : Nat}
  {List.length(&2, F.Finding, List.concat(&2, F.Finding,
      [Hoist.let_hit(hot, kids, body, rest, self, wides, carried, path),
        Hoist.walk(kids, self, wides, carried, path, hot), Hoist.walk(body, self, wides, carried, path, hot),
        Hoist.walk(rest, self, wides, carried, path, hot)]))
    == Nat.add(Bool.pick(Nat, Laws.hoist.let(hot, kids, body, rest, self, wides, carried), 1n, 0n),
      Nat.add(Laws.hoist.count(kids, self, wides, carried, hot),
        Nat.add(Laws.hoist.count(body, self, wides, carried, hot), Laws.hoist.count(rest, self, wides, carried, hot))))
    : Nat}

def hoist.plain(kids, body, rest, self, wides, carried, path, hot, ih1, ih2, ih3):
  +own = Hoist.let_hit(hot, kids, body, rest, self, wides, carried, path)
  +wk = Hoist.walk(kids, self, wides, carried, path, hot)
  +wb = Hoist.walk(body, self, wides, carried, path, hot)
  +wr = Hoist.walk(rest, self, wides, carried, path, hot)
  +ck = Laws.hoist.count(kids, self, wides, carried, hot)
  +cb = Laws.hoist.count(body, self, wides, carried, hot)
  +cr = Laws.hoist.count(rest, self, wides, carried, hot)
  hoist.front(own, List.concat(&2, F.Finding, [wk, wb, wr]),
    Bool.pick(Nat, Laws.hoist.let(hot, kids, body, rest, self, wides, carried), 1n, 0n),
    Nat.add(ck, Nat.add(cb, cr)),
    hoist.let(hot, kids, body, rest, self, wides, carried, path),
    M1.chars.sum(wk, wb, wr, ck, cb, cr, ih1, ih2, ih3))

# hoist's walk counts the calls and lets the law counts, at every heat
law hoist.walk:
  for nn: Tree.Node
  for +self: String
  for +wides: List<&2, String>
  for +carried: List<&2, String>
  for +path: String
  for +hot: Bool
  {List.length(&2, F.Finding, Hoist.walk(nn, self, wides, carried, path, hot))
    == Laws.hoist.count(nn, self, wides, carried, hot) : Nat}

def hoist.walk(nn, self, wides, carried, path, hot):
  match nn:
    case Tree.Leaf{tok}:
      {==}
    case Tree.Group{o, gk, cl}:
      {==}
    case Tree.Stmt{kind, sk, sb}:
      {==}
    case Tree.NNil{}:
      {==}
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{Lex.Tok{+k, +t, l, c}}:
          match rest:
            case Tree.Leaf{tok}:
              {==}
            case Tree.Group{o, gk, cl}:
              {==}
            case Tree.Stmt{kind, sk, sb}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{rh, +rr}:
              match rh:
                case Tree.Group{Lex.Tok{gk, +o, gl, gc}, +kids, cl}:
                  hoist.site(k, t, o, kids, rr, self, wides, carried, path, hot,
                    hoist.walk(kids, self, wides, carried, path, Hoist.warm(hot, k)),
                    hoist.walk(rr, self, wides, carried, path, Hoist.warm(hot, k)))
                case Tree.Leaf{tok}:
                  hoist.walk(rest, self, wides, carried, path, Hoist.warm(hot, k))
                case Tree.Stmt{kind, sk, sb}:
                  hoist.walk(rest, self, wides, carried, path, Hoist.warm(hot, k))
                case Tree.NNil{}:
                  hoist.walk(rest, self, wides, carried, path, Hoist.warm(hot, k))
                case Tree.NCons{nh, nt}:
                  hoist.walk(rest, self, wides, carried, path, Hoist.warm(hot, k))
        case Tree.Group{o, +kids, cl}:
          M1.index.two(Hoist.walk(kids, self, wides, carried, path, hot),
            Hoist.walk(rest, self, wides, carried, path, hot),
            Laws.hoist.count(kids, self, wides, carried, hot), Laws.hoist.count(rest, self, wides, carried, hot),
            hoist.walk(kids, self, wides, carried, path, hot), hoist.walk(rest, self, wides, carried, path, hot))
        case Tree.Stmt{kind, +kids, +body}:
          match kind:
            case Tree.SCase{}:
              hoist.arm(kids, body, rest, self, wides, carried, path, hot,
                hoist.walk(kids, self, wides, carried, path, False{}),
                hoist.walk(body, self, wides, carried, path, Bool.and(hot, Calls.calls(body, self))),
                hoist.walk(rest, self, wides, carried, path, hot))
            case Tree.SDef{}:
              hoist.plain(kids, body, rest, self, wides, carried, path, hot,
                hoist.walk(kids, self, wides, carried, path, hot),
                hoist.walk(body, self, wides, carried, path, hot), hoist.walk(rest, self, wides, carried, path, hot))
            case Tree.SType{}:
              hoist.plain(kids, body, rest, self, wides, carried, path, hot,
                hoist.walk(kids, self, wides, carried, path, hot),
                hoist.walk(body, self, wides, carried, path, hot), hoist.walk(rest, self, wides, carried, path, hot))
            case Tree.SLaw{}:
              hoist.plain(kids, body, rest, self, wides, carried, path, hot,
                hoist.walk(kids, self, wides, carried, path, hot),
                hoist.walk(body, self, wides, carried, path, hot), hoist.walk(rest, self, wides, carried, path, hot))
            case Tree.SImport{}:
              hoist.plain(kids, body, rest, self, wides, carried, path, hot,
                hoist.walk(kids, self, wides, carried, path, hot),
                hoist.walk(body, self, wides, carried, path, hot), hoist.walk(rest, self, wides, carried, path, hot))
            case Tree.SFor{}:
              hoist.plain(kids, body, rest, self, wides, carried, path, hot,
                hoist.walk(kids, self, wides, carried, path, hot),
                hoist.walk(body, self, wides, carried, path, hot), hoist.walk(rest, self, wides, carried, path, hot))
            case Tree.SLet{}:
              hoist.plain(kids, body, rest, self, wides, carried, path, hot,
                hoist.walk(kids, self, wides, carried, path, hot),
                hoist.walk(body, self, wides, carried, path, hot), hoist.walk(rest, self, wides, carried, path, hot))
            case Tree.STerm{}:
              hoist.plain(kids, body, rest, self, wides, carried, path, hot,
                hoist.walk(kids, self, wides, carried, path, hot),
                hoist.walk(body, self, wides, carried, path, hot), hoist.walk(rest, self, wides, carried, path, hot))
        case Tree.NNil{}:
          hoist.walk(rest, self, wides, carried, path, hot)
        case Tree.NCons{nh, nt}:
          hoist.walk(rest, self, wides, carried, path, hot)

# a def that calls itself and is not exempt gathers its walk, entered hot,
# any other nothing
law hoist.def:
  for g: Bool
  for +body: Tree.Node
  for +self: String
  for +wides: List<&2, String>
  for +carried: List<&2, String>
  for +path: String
  {List.length(&2, F.Finding,
      Lazy.stop(List<&2, F.Finding>, Bool.not(g), [], _u => Hoist.walk(body, self, wides, carried, path, True{})))
    == Bool.pick(Nat, g, Laws.hoist.count(body, self, wides, carried, True{}), 0n) : Nat}

def hoist.def(g, body, self, wides, carried, path):
  match g:
    case True{}:
      hoist.walk(body, self, wides, carried, path, True{})
    case False{}:
      {==}

# over the defs, the rule's join counts what it gathered and what the law
# counts
law hoist.go:
  for ds: List<&2, Calls.Def>
  for +wides: List<&2, String>
  for +path: String
  for +acc: List<&2, List<&2, F.Finding>>
  {List.length(&2, F.Finding, Hoist.check.go(ds, wides, path, acc))
    == Nat.add(M1.index.sum(acc), Laws.hoist.total(ds, wides, path)) : Nat}

def hoist.go(ds, wides, path, acc):
  match ds:
    case Nil{}:
      M1.index.flat(acc, Nil{})
    case Con{Calls.Def{+name, +sig, +body}, +rest}:
      +g = Bool.and(Calls.calls(body, name), Bool.not(Calls.exempt(path, sig)))
      +carried = Hoist.carried(sig, body, name)
      +x = Lazy.stop(List<&2, F.Finding>, Bool.not(g), [], _u => Hoist.walk(body, name, wides, carried, path, True{}))
      +n = Bool.pick(Nat, g, Laws.hoist.count(body, name, wides, carried, True{}), 0n)
      +tot = Laws.hoist.total(rest, wides, path)
      Equal.trans(Nat,
        List.length(&2, F.Finding, Hoist.check.go(rest, wides, path, x <> acc)),
        Nat.add(Nat.add(M1.index.sum(acc), List.length(&2, F.Finding, x)), tot),
        Nat.add(M1.index.sum(acc), Nat.add(n, tot)),
        hoist.go(rest, wides, path, x <> acc),
        Equal.trans(Nat,
          Nat.add(Nat.add(M1.index.sum(acc), List.length(&2, F.Finding, x)), tot),
          Nat.add(M1.index.sum(acc), Nat.add(List.length(&2, F.Finding, x), tot)),
          Nat.add(M1.index.sum(acc), Nat.add(n, tot)),
          M1.index.assoc(M1.index.sum(acc), List.length(&2, F.Finding, x), tot),
          Equal.cong(Nat, Nat, z => Nat.add(M1.index.sum(acc), Nat.add(z, tot)), List.length(&2, F.Finding, x), n,
            hoist.def(g, body, name, wides, carried, path))))

def Laws.hoist_counts(path, _text, _toks, tree, _bound, _items):
  +ds = Calls.defs(tree)
  hoist.go(ds, Hoist.wide_defs(ds, Nil{}), path, Nil{})
