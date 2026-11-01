# proofs of laws/TailReportsNonTailCalls.bend
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/lazy/lazy.bend as Lazy
import ../src/syntax/tree.bend as Tree
import ../src/rules/calls.bend as Calls
import ../src/rules/correctness/pick.bend as Pick
import ../src/rules/pedantic/tail.bend as Tail
import ../laws/TailReportsNonTailCalls.bend as Laws
import ./lemmas/Nat.bend as M1
import ./lemmas/Pick.bend as M2

# tail (laws/TailReportsNonTailCalls.bend): the walk counts the self-calls Laws.tail.count
# counts, and the def walk sums them over the defs Laws.tail.total keeps.

# a pick between no findings and a list counts 0 or the list's count
law tail.drop:
  for b: Bool
  for -xs: List<&2, F.Finding>
  for -m: Nat
  for ih: {List.length(&2, F.Finding, xs) == m : Nat}
  {List.length(&2, F.Finding, Bool.pick(List<&2, F.Finding>, b, [], xs)) == Bool.pick(Nat, b, 0n, m) : Nat}

def tail.drop(b, _xs, _m, ih):
  match b:
    case True{}:
      {==}
    case False{}:
      ih

# a successor on the right comes out in front
law tail.succ:
  for a: Nat
  for -b: Nat
  {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}

def tail.succ(a, b):
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(p, 1n+b), 1n+Nat.add(p, b), tail.succ(p, b))

# addition commutes
law tail.comm:
  for a: Nat
  for +b: Nat
  {Nat.add(a, b) == Nat.add(b, a) : Nat}

def tail.comm(a, b):
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, M2.tail.zero(b))
    case 1n+p:
      Equal.trans(Nat, 1n+Nat.add(p, b), 1n+Nat.add(b, p), Nat.add(b, 1n+p),
        Equal.cong(Nat, Nat, x => 1n+x, Nat.add(p, b), Nat.add(b, p), tail.comm(p, b)),
        Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), tail.succ(b, p)))

# addition associates
law tail.assoc:
  for a: Nat
  for -b: Nat
  for -c: Nat
  {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}

def tail.assoc(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(Nat.add(p, b), c), Nat.add(p, Nat.add(b, c)), tail.assoc(p, b, c))

# and with False is False
law tail.andf:
  for x: Bool
  {Bool.and(x, False{}) == False{} : Bool}

def tail.andf(x):
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

# a head that is not a group after a name: no tail-call test holds
law tail.nongroup:
  for +t: String
  for +name: String
  {Bool.and(String.eq(t, name), False{}) == False{} : Bool}

def tail.nongroup(t, name):
  tail.andf(String.eq(t, name))

# the rule's tail-call test is the law's whole-chain test
law tail.bare:
  for kids: Tree.Node
  for +name: String
  {Tail.bare(kids, name) == Laws.tail.whole(kids, name) : Bool}

def tail.bare(kids, name):
  match kids:
    case Tree.NCons{h, +r}:
      match h:
        case Tree.Leaf{Lex.Tok{k, +t, l, c}}:
          match r:
            case Tree.NCons{g, +r2}:
              match g:
                case Tree.Group{Lex.Tok{k2, o, l2, c2}, gk, cl}:
                  match r2:
                    case Tree.Leaf{y}:
                      {==}
                    case Tree.Group{e, f, i}:
                      {==}
                    case Tree.Stmt{e, f, i}:
                      {==}
                    case Tree.NNil{}:
                      {==}
                    case Tree.NCons{e, f}:
                      {==}
                case Tree.Leaf{x}:
                  match r2:
                    case Tree.Leaf{y}:
                      {==}
                    case Tree.Group{e, f, i}:
                      {==}
                    case Tree.Stmt{e, f, i}:
                      {==}
                    case Tree.NNil{}:
                      tail.nongroup(t, name)
                    case Tree.NCons{e, f}:
                      {==}
                case Tree.Stmt{a, b, d}:
                  match r2:
                    case Tree.Leaf{y}:
                      {==}
                    case Tree.Group{e, f, i}:
                      {==}
                    case Tree.Stmt{e, f, i}:
                      {==}
                    case Tree.NNil{}:
                      tail.nongroup(t, name)
                    case Tree.NCons{e, f}:
                      {==}
                case Tree.NNil{}:
                  match r2:
                    case Tree.Leaf{y}:
                      {==}
                    case Tree.Group{e, f, i}:
                      {==}
                    case Tree.Stmt{e, f, i}:
                      {==}
                    case Tree.NNil{}:
                      tail.nongroup(t, name)
                    case Tree.NCons{e, f}:
                      {==}
                case Tree.NCons{a, b}:
                  match r2:
                    case Tree.Leaf{y}:
                      {==}
                    case Tree.Group{e, f, i}:
                      {==}
                    case Tree.Stmt{e, f, i}:
                      {==}
                    case Tree.NNil{}:
                      tail.nongroup(t, name)
                    case Tree.NCons{e, f}:
                      {==}
            case Tree.Leaf{x}:
              {==}
            case Tree.Group{a, b, d}:
              {==}
            case Tree.Stmt{a, b, d}:
              {==}
            case Tree.NNil{}:
              {==}
        case Tree.Group{a, b, d}:
          {==}
        case Tree.Stmt{a, b, d}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{a, b}:
          {==}
    case Tree.Leaf{x}:
      {==}
    case Tree.Group{a, b, d}:
      {==}
    case Tree.Stmt{a, b, d}:
      {==}
    case Tree.NNil{}:
      {==}

# a self-call site, a name then a `(` group, onto a rest the law holds for
law tail.call:
  for k: Lex.TokKind
  for +t: String
  for +l: U32
  for +c: U32
  for k2: Lex.TokKind
  for +o: String
  for l2: U32
  for c2: U32
  for +kids: Tree.Node
  for cl: Maybe<&2, Lex.Tok>
  for +rest: Tree.Node
  for +name: String
  for +path: String
  for +skip: Bool
  for ih1: {List.length(&2, F.Finding, Tail.walk(kids, name, path, False{})) == Laws.tail.count(kids, name, False{})
    : Nat}
  for ih2: {List.length(&2, F.Finding, Tail.walk(rest, name, path, False{})) == Laws.tail.count(rest, name, False{})
    : Nat}
  {List.length(&2, F.Finding,
    Tail.walk(Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}},
      Tree.NCons{Tree.Group{Lex.Tok{k2, o, l2, c2}, kids, cl}, rest}}, name, path, skip))
    == Laws.tail.count(Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}},
      Tree.NCons{Tree.Group{Lex.Tok{k2, o, l2, c2}, kids, cl}, rest}}, name, skip) : Nat}

def tail.call(_k, t, l, c, _k2, o, _l2, _c2, kids, _cl, rest, name, path, skip, ih1, ih2):
  +pk = Bool.and(String.eq(o, "("), String.eq(t, "Bool.pick"))
  +inside = Bool.pick(List<&2, F.Finding>, pk, [], Tail.walk(kids, name, path, False{}))
  +after = Tail.walk(rest, name, path, False{})
  +m = Nat.add(Bool.pick(Nat, pk, 0n, Laws.tail.count(kids, name, False{})), Laws.tail.count(rest, name, False{}))
  M1.nat.pick(Bool.and(Bool.and(String.eq(o, "("), String.eq(t, name)), Bool.not(skip)),
    F.Finding{path, l, c, U32.from_nat(String.length(name)), "tail",
      "This call to " ++ name ++ " is not a tail call, so a long list or string overflows the stack on the JS lane; carry an accumulator."},
    List.concat(&2, F.Finding, [inside, after]), m,
    Equal.trans(Nat, List.length(&2, F.Finding, List.concat(&2, F.Finding, [inside, after])),
      Nat.add(List.length(&2, F.Finding, inside), List.length(&2, F.Finding, after)), m,
      M2.tail.cat2(inside, after),
      M2.esc.add(List.length(&2, F.Finding, inside), Bool.pick(Nat, pk, 0n, Laws.tail.count(kids, name, False{})),
        List.length(&2, F.Finding, after), Laws.tail.count(rest, name, False{}),
        tail.drop(pk, Tail.walk(kids, name, path, False{}), Laws.tail.count(kids, name, False{}), ih1), ih2)))

# a group onto a rest the law holds for
law tail.grp:
  for open: Lex.Tok
  for +kids: Tree.Node
  for close: Maybe<&2, Lex.Tok>
  for +rest: Tree.Node
  for +name: String
  for +path: String
  for skip: Bool
  for ih1: {List.length(&2, F.Finding, Tail.walk(kids, name, path, False{})) == Laws.tail.count(kids, name, False{})
    : Nat}
  for ih2: {List.length(&2, F.Finding, Tail.walk(rest, name, path, False{})) == Laws.tail.count(rest, name, False{})
    : Nat}
  {List.length(&2, F.Finding, Tail.walk(Tree.NCons{Tree.Group{open, kids, close}, rest}, name, path, skip))
    == Laws.tail.count(Tree.NCons{Tree.Group{open, kids, close}, rest}, name, skip) : Nat}

def tail.grp(_open, kids, _close, rest, name, path, _skip, ih1, ih2):
  +a = Tail.walk(kids, name, path, False{})
  +b = Tail.walk(rest, name, path, False{})
  Equal.trans(Nat, List.length(&2, F.Finding, List.concat(&2, F.Finding, [a, b])),
    Nat.add(List.length(&2, F.Finding, a), List.length(&2, F.Finding, b)),
    Nat.add(Laws.tail.count(kids, name, False{}), Laws.tail.count(rest, name, False{})),
    M2.tail.cat2(a, b),
    M2.esc.add(List.length(&2, F.Finding, a), Laws.tail.count(kids, name, False{}),
      List.length(&2, F.Finding, b), Laws.tail.count(rest, name, False{}), ih1, ih2))

# a statement onto a rest the law holds for
law tail.stmt:
  for kind: Tree.StmtKind
  for +kids: Tree.Node
  for +body: Tree.Node
  for +rest: Tree.Node
  for +name: String
  for +path: String
  for skip: Bool
  for ih1: {List.length(&2, F.Finding, Tail.walk(kids, name, path, Tail.bare(kids, name)))
    == Laws.tail.count(kids, name, Tail.bare(kids, name)) : Nat}
  for ih2: {List.length(&2, F.Finding, Tail.walk(body, name, path, False{})) == Laws.tail.count(body, name, False{})
    : Nat}
  for ih3: {List.length(&2, F.Finding, Tail.walk(rest, name, path, False{})) == Laws.tail.count(rest, name, False{})
    : Nat}
  {List.length(&2, F.Finding, Tail.walk(Tree.NCons{Tree.Stmt{kind, kids, body}, rest}, name, path, skip))
    == Laws.tail.count(Tree.NCons{Tree.Stmt{kind, kids, body}, rest}, name, skip) : Nat}

def tail.stmt(_kind, kids, body, rest, name, path, _skip, ih1, ih2, ih3):
  +a = Tail.walk(kids, name, path, Tail.bare(kids, name))
  +b = Tail.walk(body, name, path, False{})
  +r = Tail.walk(rest, name, path, False{})
  Equal.trans(Nat, List.length(&2, F.Finding, List.concat(&2, F.Finding, [a, b, r])),
    Nat.add(List.length(&2, F.Finding, a), Nat.add(List.length(&2, F.Finding, b), List.length(&2, F.Finding, r))),
    Nat.add(Laws.tail.count(kids, name, Laws.tail.whole(kids, name)),
      Nat.add(Laws.tail.count(body, name, False{}), Laws.tail.count(rest, name, False{}))),
    M2.tail.cat3(a, b, r),
    M2.esc.add(List.length(&2, F.Finding, a), Laws.tail.count(kids, name, Laws.tail.whole(kids, name)),
      Nat.add(List.length(&2, F.Finding, b), List.length(&2, F.Finding, r)),
      Nat.add(Laws.tail.count(body, name, False{}), Laws.tail.count(rest, name, False{})),
      Equal.trans(Nat, List.length(&2, F.Finding, a), Laws.tail.count(kids, name, Tail.bare(kids, name)),
        Laws.tail.count(kids, name, Laws.tail.whole(kids, name)), ih1,
        Equal.cong(Bool, Nat, z => Laws.tail.count(kids, name, z), Tail.bare(kids, name),
          Laws.tail.whole(kids, name), tail.bare(kids, name))),
      M2.esc.add(List.length(&2, F.Finding, b), Laws.tail.count(body, name, False{}),
        List.length(&2, F.Finding, r), Laws.tail.count(rest, name, False{}), ih2, ih3)))

def Laws.tail_walk_counts(nn, name, path, skip):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{Lex.Tok{k, t, l, c}}:
          match rest:
            case Tree.NCons{h2, +r2}:
              match h2:
                case Tree.Group{Lex.Tok{k2, o, l2, c2}, +kids, cl}:
                  tail.call(k, t, l, c, k2, o, l2, c2, kids, cl, r2, name, path, skip,
                    Laws.tail_walk_counts(kids, name, path, False{}), Laws.tail_walk_counts(r2, name, path, False{}))
                case Tree.Leaf{x}:
                  Laws.tail_walk_counts(rest, name, path, False{})
                case Tree.Stmt{a, b, d}:
                  Laws.tail_walk_counts(rest, name, path, False{})
                case Tree.NNil{}:
                  Laws.tail_walk_counts(rest, name, path, False{})
                case Tree.NCons{a, b}:
                  Laws.tail_walk_counts(rest, name, path, False{})
            case Tree.Leaf{x}:
              Laws.tail_walk_counts(rest, name, path, False{})
            case Tree.Group{a, b, d}:
              Laws.tail_walk_counts(rest, name, path, False{})
            case Tree.Stmt{a, b, d}:
              Laws.tail_walk_counts(rest, name, path, False{})
            case Tree.NNil{}:
              Laws.tail_walk_counts(rest, name, path, False{})
        case Tree.Group{open, +kids, close}:
          tail.grp(open, kids, close, rest, name, path, skip,
            Laws.tail_walk_counts(kids, name, path, False{}), Laws.tail_walk_counts(rest, name, path, False{}))
        case Tree.Stmt{kind, +kids, +body}:
          tail.stmt(kind, kids, body, rest, name, path, skip,
            Laws.tail_walk_counts(kids, name, path, Tail.bare(kids, name)),
            Laws.tail_walk_counts(body, name, path, False{}), Laws.tail_walk_counts(rest, name, path, False{}))
        case Tree.NNil{}:
          Laws.tail_walk_counts(rest, name, path, False{})
        case Tree.NCons{a, b}:
          Laws.tail_walk_counts(rest, name, path, False{})
    case Tree.Leaf{x}:
      {==}
    case Tree.Group{a, b, d}:
      {==}
    case Tree.Stmt{a, b, d}:
      {==}
    case Tree.NNil{}:
      {==}

# the total count of a list of finding lists
def tail.lens(xss: List<&2, List<&2, F.Finding>>) -> Nat:
  match xss:
    case Nil{}:
      0n
    case Con{h, t}:
      Nat.add(List.length(&2, F.Finding, h), tail.lens(t))

# joined finding lists count what they count apart
law tail.flat:
  for xss: List<&2, List<&2, F.Finding>>
  {List.length(&2, F.Finding, List.concat(&2, F.Finding, xss)) == tail.lens(xss) : Nat}

def tail.flat(xss):
  match xss:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Equal.trans(Nat, List.length(&2, F.Finding, List.append(&2, F.Finding, h, List.concat(&2, F.Finding, t))),
        Nat.add(List.length(&2, F.Finding, h), List.length(&2, F.Finding, List.concat(&2, F.Finding, t))),
        Nat.add(List.length(&2, F.Finding, h), tail.lens(t)),
        M2.esc.app(h, List.concat(&2, F.Finding, t)),
        Equal.cong(Nat, Nat, x => Nat.add(List.length(&2, F.Finding, h), x),
          List.length(&2, F.Finding, List.concat(&2, F.Finding, t)), tail.lens(t), tail.flat(t)))

# reversing finding lists onto an accumulator keeps their total count
law tail.rev:
  for xs: List<&2, List<&2, F.Finding>>
  for +acc: List<&2, List<&2, F.Finding>>
  {tail.lens(List.reverse.go(&2, List<&2, F.Finding>, xs, acc)) == Nat.add(tail.lens(xs), tail.lens(acc)) : Nat}

def tail.rev(xs, acc):
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Equal.trans(Nat, tail.lens(List.reverse.go(&2, List<&2, F.Finding>, t, h <> acc)),
        Nat.add(tail.lens(t), Nat.add(List.length(&2, F.Finding, h), tail.lens(acc))),
        Nat.add(Nat.add(List.length(&2, F.Finding, h), tail.lens(t)), tail.lens(acc)),
        tail.rev(t, h <> acc),
        Equal.trans(Nat, Nat.add(tail.lens(t), Nat.add(List.length(&2, F.Finding, h), tail.lens(acc))),
          Nat.add(Nat.add(tail.lens(t), List.length(&2, F.Finding, h)), tail.lens(acc)),
          Nat.add(Nat.add(List.length(&2, F.Finding, h), tail.lens(t)), tail.lens(acc)),
          Equal.sym(Nat, Nat.add(Nat.add(tail.lens(t), List.length(&2, F.Finding, h)), tail.lens(acc)),
            Nat.add(tail.lens(t), Nat.add(List.length(&2, F.Finding, h), tail.lens(acc))),
            tail.assoc(tail.lens(t), List.length(&2, F.Finding, h), tail.lens(acc))),
          Equal.cong(Nat, Nat, x => Nat.add(x, tail.lens(acc)),
            Nat.add(tail.lens(t), List.length(&2, F.Finding, h)),
            Nat.add(List.length(&2, F.Finding, h), tail.lens(t)),
            tail.comm(tail.lens(t), List.length(&2, F.Finding, h)))))

# the def walk counts what it has gathered and what the defs left hold
law tail.defs:
  for ds: List<&2, Calls.Def>
  for +path: String
  for +acc: List<&2, List<&2, F.Finding>>
  {List.length(&2, F.Finding, Tail.check.go(ds, path, acc))
    == Nat.add(tail.lens(acc), Laws.tail.total(ds, path)) : Nat}

def tail.defs(ds, path, acc):
  match ds:
    case Nil{}:
      Equal.trans(Nat,
        List.length(&2, F.Finding, List.concat(&2, F.Finding, List.reverse(&2, List<&2, F.Finding>, acc))),
        tail.lens(List.reverse(&2, List<&2, F.Finding>, acc)), Nat.add(tail.lens(acc), 0n),
        tail.flat(List.reverse(&2, List<&2, F.Finding>, acc)), tail.rev(acc, Nil{}))
    case Con{Calls.Def{+name, +sig, +body}, +rest}:
      +keep = Bool.and(Calls.seq(sig), Bool.not(Calls.exempt(path, sig)))
      +xs = Lazy.stop(List<&2, F.Finding>, Bool.not(keep), [], _u => Tail.walk(body, name, path, False{}))
      +cnt = Bool.pick(Nat, keep, Laws.tail.count(body, name, False{}), 0n)
      +lx = List.length(&2, F.Finding, xs)
      +tot = Laws.tail.total(rest, path)
      +la = tail.lens(acc)
      Equal.trans(Nat, List.length(&2, F.Finding, Tail.check.go(rest, path, xs <> acc)),
        Nat.add(Nat.add(lx, la), tot), Nat.add(la, Nat.add(cnt, tot)),
        tail.defs(rest, path, xs <> acc),
        Equal.trans(Nat, Nat.add(Nat.add(lx, la), tot), Nat.add(Nat.add(la, lx), tot), Nat.add(la, Nat.add(cnt, tot)),
          Equal.cong(Nat, Nat, x => Nat.add(x, tot), Nat.add(lx, la), Nat.add(la, lx), tail.comm(lx, la)),
          Equal.trans(Nat, Nat.add(Nat.add(la, lx), tot), Nat.add(la, Nat.add(lx, tot)), Nat.add(la, Nat.add(cnt, tot)),
            tail.assoc(la, lx, tot),
            Equal.cong(Nat, Nat, x => Nat.add(la, Nat.add(x, tot)), lx, cnt,
              M2.tail.stop(keep, Tail.walk(body, name, path, False{}), Laws.tail.count(body, name, False{}),
                Laws.tail_walk_counts(body, name, path, False{}))))))

def Laws.tail_counts(path, _text, _toks, tree, _bound, _items):
  tail.defs(Calls.defs(tree), path, Nil{})
