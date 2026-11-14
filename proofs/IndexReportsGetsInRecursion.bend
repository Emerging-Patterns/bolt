# proofs of laws/IndexReportsGetsInRecursion.bend
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/lazy/lazy.bend as Lazy
import ../src/syntax/tree.bend as Tree
import ../src/rules/calls.bend as Calls
import ../src/rules/pedantic/index.bend as Index
import ../src/rules/table.bend as Table
import ../laws/IndexReportsGetsInRecursion.bend as Laws
import ./lemmas/MatchStatementCounts.bend as M1
import ./lemmas/Nat.bend as M2

# The recursion rule, index: its literal test is the law's, its fire test is
# the law's (a List.get held by a fixed table is exactly one
# src/rules/table.bend calls one), each call adds what the law counts, and the def walk joins the
# per-def lists into their sum.

# the rule's literal test is the law's
law index.lit:
  for n: Tree.Node
  {Index.literal(n) == Laws.index.lit(n) : Bool}

def index.lit(n):
  match n:
    case Tree.Leaf{tok}:
      {==}
    case Tree.Group{o, gk, cl}:
      {==}
    case Tree.Stmt{kind, sk, sb}:
      {==}
    case Tree.NNil{}:
      {==}
    case Tree.NCons{h, rest}:
      match h:
        case Tree.Group{o, gk, cl}:
          {==}
        case Tree.Stmt{kind, sk, sb}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{nh, nt}:
          {==}
        case Tree.Leaf{Lex.Tok{kind, t, l, c}}:
          match kind:
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
              match rest:
                case Tree.Leaf{tok}:
                  {==}
                case Tree.Group{o, gk, cl}:
                  {==}
                case Tree.Stmt{sk, skids, sb}:
                  {==}
                case Tree.NNil{}:
                  {==}
                case Tree.NCons{nh, nt}:
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

# table's literal test is the law's too
law index.tlit:
  for n: Tree.Node
  {Table.literal(n) == Laws.index.lit(n) : Bool}

def index.tlit(n):
  match n:
    case Tree.Leaf{tok}:
      {==}
    case Tree.Group{o, gk, cl}:
      {==}
    case Tree.Stmt{kind, sk, sb}:
      {==}
    case Tree.NNil{}:
      {==}
    case Tree.NCons{h, rest}:
      match h:
        case Tree.Group{o, gk, cl}:
          {==}
        case Tree.Stmt{kind, sk, sb}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{nh, nt}:
          {==}
        case Tree.Leaf{Lex.Tok{kind, t, l, c}}:
          match kind:
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
              match rest:
                case Tree.Leaf{tok}:
                  {==}
                case Tree.Group{o, gk, cl}:
                  {==}
                case Tree.Stmt{sk, skids, sb}:
                  {==}
                case Tree.NNil{}:
                  {==}
                case Tree.NCons{nh, nt}:
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

# a List.get whose index is not a literal: index reports it exactly when its
# list is not a fixed table, which is exactly when table does not
law index.gate:
  for a: Bool
  for o: Bool
  for -x: F.Finding
  {Bool.and(Bool.not(a), Bool.not(o))
    == Bool.and(Bool.not(a),
      List.is_empty(&2, F.Finding, Bool.pick(List<&2, F.Finding>, Bool.and(Bool.not(a), o), [x], []))) : Bool}

def index.gate(a, o, _x):
  match a:
    case True{}:
      {==}
    case False{}:
      match o:
        case True{}:
          {==}
        case False{}:
          {==}

# a String.get's test, the held test dropped
law index.tail:
  for sb: Bool
  for a: Bool
  {Bool.and(sb, Bool.and(Bool.not(a), True{})) == Bool.and(sb, Bool.not(a)) : Bool}

def index.tail(sb, a):
  match sb:
    case False{}:
      {==}
    case True{}:
      match a:
        case True{}:
          {==}
        case False{}:
          {==}

# the rule's fire test for a call is the law's
law index.fire:
  for list: Bool
  for ob: Bool
  for +sb: Bool
  for +kids: Tree.Node
  for +fixed: List<&2, String>
  for +path: String
  for +l: U32
  for +c: U32
  {Bool.and(Bool.and(ob, Bool.or(list, sb)),
      Bool.and(Bool.not(Index.literal(Calls.arg(Calls.args(kids), Bool.pick(Nat, list, 3n, 1n)))),
        Bool.not(Index.held(list, Calls.arg(Calls.args(kids), 2n), fixed))))
    == Laws.index.fires(list, ob, sb, Calls.args(kids), Table.hit(ob, "List.get", kids, fixed, path, l, c)) : Bool}

def index.fire(list, ob, sb, kids, fixed, path, l, c):
  match list:
    case True{}:
      match ob:
        case False{}:
          {==}
        case True{}:
          +a3 = Calls.arg(Calls.args(kids), 3n)
          +own = Table.owns(Calls.arg(Calls.args(kids), 2n), fixed)
          +x = Table.cite(True{}, path, l, c, U32.from_nat(String.length("List.get")))
          Equal.trans(Bool,
            Bool.and(Bool.not(Index.literal(a3)), Bool.not(own)),
            Bool.and(Bool.not(Laws.index.lit(a3)), Bool.not(own)),
            Bool.and(Bool.not(Laws.index.lit(a3)), List.is_empty(&2, F.Finding,
              Bool.pick(List<&2, F.Finding>, Bool.and(Bool.not(Table.literal(a3)), own), [x], []))),
            Equal.cong(Bool, Bool, z => Bool.and(Bool.not(z), Bool.not(own)),
              Index.literal(a3), Laws.index.lit(a3), index.lit(a3)),
            Equal.trans(Bool,
              Bool.and(Bool.not(Laws.index.lit(a3)), Bool.not(own)),
              Bool.and(Bool.not(Laws.index.lit(a3)), List.is_empty(&2, F.Finding,
                Bool.pick(List<&2, F.Finding>, Bool.and(Bool.not(Laws.index.lit(a3)), own), [x], []))),
              Bool.and(Bool.not(Laws.index.lit(a3)), List.is_empty(&2, F.Finding,
                Bool.pick(List<&2, F.Finding>, Bool.and(Bool.not(Table.literal(a3)), own), [x], []))),
              index.gate(Laws.index.lit(a3), own, x),
              Equal.cong(Bool, Bool,
                z => Bool.and(Bool.not(Laws.index.lit(a3)), List.is_empty(&2, F.Finding,
                  Bool.pick(List<&2, F.Finding>, Bool.and(Bool.not(z), own), [x], []))),
                Laws.index.lit(a3), Table.literal(a3),
                Equal.sym(Bool, Table.literal(a3), Laws.index.lit(a3), index.tlit(a3)))))
    case False{}:
      match ob:
        case False{}:
          {==}
        case True{}:
          +a1 = Calls.arg(Calls.args(kids), 1n)
          Equal.trans(Bool,
            Bool.and(sb, Bool.and(Bool.not(Index.literal(a1)), True{})),
            Bool.and(sb, Bool.and(Bool.not(Laws.index.lit(a1)), True{})),
            Bool.and(sb, Bool.not(Laws.index.lit(a1))),
            Equal.cong(Bool, Bool, z => Bool.and(sb, Bool.and(Bool.not(z), True{})),
              Index.literal(a1), Laws.index.lit(a1), index.lit(a1)),
            index.tail(sb, Laws.index.lit(a1)))

# a count one higher when b holds is b's one or none, then the count
law index.one:
  for b: Bool
  for -m: Nat
  {Bool.pick(Nat, b, 1n+m, m) == Nat.add(Bool.pick(Nat, b, 1n, 0n), m) : Nat}

def index.one(b, _m):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# a call onto the rest: its own finding, then its group's and the rest's
law index.call:
  for +k: Lex.TokKind
  for +t: String
  for +l: U32
  for +c: U32
  for +gk: Lex.TokKind
  for +o: String
  for +gl: U32
  for +gc: U32
  for +kids: Tree.Node
  for +cl: Maybe<&2, Lex.Tok>
  for +r: Tree.Node
  for +path: String
  for +fixed: List<&2, String>
  for +self: String
  for ih1: {List.length(&2, F.Finding, Index.walk(kids, path, fixed, self)) == Laws.index.count(kids, path, fixed, self)
    : Nat}
  for ih2: {List.length(&2, F.Finding, Index.walk(r, path, fixed, self)) == Laws.index.count(r, path, fixed, self)
    : Nat}
  {List.length(&2, F.Finding, Index.walk(Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}},
      Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, kids, cl}, r}}, path, fixed, self))
    == Laws.index.count(Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}},
      Tree.NCons{Tree.Group{Lex.Tok{gk, o, gl, gc}, kids, cl}, r}}, path, fixed, self) : Nat}

def index.call(_k, t, l, c, _gk, o, _gl, _gc, kids, _cl, r, path, fixed, self, ih1, ih2):
  +list = Index.named(t, self, "List.get")
  +ob = String.eq(o, "(")
  +sb = Index.named(t, self, "String.get")
  +as = Calls.args(kids)
  +fire = Bool.and(Bool.and(ob, Bool.or(list, sb)),
    Bool.and(Bool.not(Index.literal(Calls.arg(as, Bool.pick(Nat, list, 3n, 1n)))),
      Bool.not(Index.held(list, Calls.arg(as, 2n), fixed))))
  +more = List.concat(&2, F.Finding, [Index.walk(kids, path, fixed, self), Index.walk(r, path, fixed, self)])
  +m = Nat.add(Laws.index.count(kids, path, fixed, self), Laws.index.count(r, path, fixed, self))
  +spec = Laws.index.fires(list, ob, sb, as, Table.hit(ob, "List.get", kids, fixed, path, l, c))
  +x = {F.Finding{path, l, c, U32.from_nat(String.length(t)), "index",
    t ++ " in a recursive def walks the list from its head on every step, which is quadratic; recurse over the list itself."}
    : F.Finding}
  Equal.trans(Nat,
    List.length(&2, F.Finding, Bool.pick(List<&2, F.Finding>, fire, x <> more, more)),
    Bool.pick(Nat, fire, 1n+m, m),
    Nat.add(Bool.pick(Nat, spec, 1n, 0n), m),
    M2.nat.pick(fire, x, more, m, M1.index.two(Index.walk(kids, path, fixed, self), Index.walk(r, path, fixed, self),
      Laws.index.count(kids, path, fixed, self), Laws.index.count(r, path, fixed, self), ih1, ih2)),
    Equal.trans(Nat,
      Bool.pick(Nat, fire, 1n+m, m),
      Nat.add(Bool.pick(Nat, fire, 1n, 0n), m),
      Nat.add(Bool.pick(Nat, spec, 1n, 0n), m),
      index.one(fire, m),
      Equal.cong(Bool, Nat, z => Nat.add(Bool.pick(Nat, z, 1n, 0n), m), fire, spec,
        index.fire(list, ob, sb, kids, fixed, path, l, c))))

# index's walk counts the calls the law counts
law index.walk:
  for n: Tree.Node
  for +path: String
  for +fixed: List<&2, String>
  for +self: String
  {List.length(&2, F.Finding, Index.walk(n, path, fixed, self)) == Laws.index.count(n, path, fixed, self) : Nat}

def index.walk(n, path, fixed, self):
  match n:
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
        case Tree.Leaf{Lex.Tok{k, t, l, c}}:
          match rest:
            case Tree.Leaf{tok}:
              {==}
            case Tree.Group{o, gk, cl}:
              {==}
            case Tree.Stmt{kind, sk, sb}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{rh, +r}:
              match rh:
                case Tree.Group{Lex.Tok{gk, o, gl, gc}, +kids, cl}:
                  index.call(k, t, l, c, gk, o, gl, gc, kids, cl, r, path, fixed, self,
                    index.walk(kids, path, fixed, self), index.walk(r, path, fixed, self))
                case Tree.Leaf{tok}:
                  index.walk(rest, path, fixed, self)
                case Tree.Stmt{kind, sk, sb}:
                  index.walk(rest, path, fixed, self)
                case Tree.NNil{}:
                  index.walk(rest, path, fixed, self)
                case Tree.NCons{nh, nt}:
                  index.walk(rest, path, fixed, self)
        case Tree.Group{o, +kids, cl}:
          M1.index.two(Index.walk(kids, path, fixed, self), Index.walk(rest, path, fixed, self),
            Laws.index.count(kids, path, fixed, self), Laws.index.count(rest, path, fixed, self),
            index.walk(kids, path, fixed, self), index.walk(rest, path, fixed, self))
        case Tree.Stmt{kind, +kids, +body}:
          M1.chars.sum(Index.walk(kids, path, fixed, self), Index.walk(body, path, fixed, self),
            Index.walk(rest, path, fixed, self),
            Laws.index.count(kids, path, fixed, self), Laws.index.count(body, path, fixed, self),
            Laws.index.count(rest, path, fixed, self),
            index.walk(kids, path, fixed, self), index.walk(body, path, fixed, self),
            index.walk(rest, path, fixed, self))
        case Tree.NNil{}:
          index.walk(rest, path, fixed, self)
        case Tree.NCons{nh, nt}:
          index.walk(rest, path, fixed, self)

# a def that calls itself and is not exempt gathers its walk, any other
# nothing
law index.def:
  for g: Bool
  for +body: Tree.Node
  for +path: String
  for +fixed: List<&2, String>
  for +self: String
  {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, Bool.not(g), [], _u => Index.walk(body, path, fixed,
      self)))
    == Bool.pick(Nat, g, Laws.index.count(body, path, fixed, self), 0n) : Nat}

def index.def(g, body, path, fixed, self):
  match g:
    case True{}:
      index.walk(body, path, fixed, self)
    case False{}:
      {==}

# over the defs, the rule's join counts what it gathered and what the law
# counts
law index.go:
  for ds: List<&2, Calls.Def>
  for +mods: List<&2, String>
  for +path: String
  for +acc: List<&2, List<&2, F.Finding>>
  {List.length(&2, F.Finding, Index.check.go(ds, mods, path, acc))
    == Nat.add(M1.index.sum(acc), Laws.index.total(ds, mods, path)) : Nat}

def index.go(ds, mods, path, acc):
  match ds:
    case Nil{}:
      M1.index.flat(acc, Nil{})
    case Con{Calls.Def{+name, +sig, +body}, +rest}:
      +g = Bool.and(Calls.calls(body, name), Bool.not(Calls.exempt(path, sig)))
      +fixed = Table.scope(body, mods)
      +x = Lazy.stop(List<&2, F.Finding>, Bool.not(g), [], _u => Index.walk(body, path, fixed, name))
      +n = Bool.pick(Nat, g, Laws.index.count(body, path, fixed, name), 0n)
      +tot = Laws.index.total(rest, mods, path)
      Equal.trans(Nat,
        List.length(&2, F.Finding, Index.check.go(rest, mods, path, x <> acc)),
        Nat.add(Nat.add(M1.index.sum(acc), List.length(&2, F.Finding, x)), tot),
        Nat.add(M1.index.sum(acc), Nat.add(n, tot)),
        index.go(rest, mods, path, x <> acc),
        Equal.trans(Nat,
          Nat.add(Nat.add(M1.index.sum(acc), List.length(&2, F.Finding, x)), tot),
          Nat.add(M1.index.sum(acc), Nat.add(List.length(&2, F.Finding, x), tot)),
          Nat.add(M1.index.sum(acc), Nat.add(n, tot)),
          M1.index.assoc(M1.index.sum(acc), List.length(&2, F.Finding, x), tot),
          Equal.cong(Nat, Nat, z => Nat.add(M1.index.sum(acc), Nat.add(z, tot)), List.length(&2, F.Finding, x), n,
            index.def(g, body, path, fixed, name))))

def Laws.index_counts(path, _text, _toks, tree, _bound, _items):
  +ds = Calls.defs(tree)
  index.go(ds, Table.modules(ds, Nil{}), path, Nil{})
