# proofs of laws/BinderResolvesInnermostFirst.bend
import Base
import ../src/syntax/lex.bend as Lex
import ../src/syntax/tree.bend as Tree
import ../src/lazy/lazy.bend as Lazy
import ../src/syntax/bind.bend as Bind
import ../laws/BinderResolvesInnermostFirst.bend as Laws
import ./lemmas/LexAndTreeFacts.bend as M1
import ./lemmas/CarriedSearch.bend as CS
import ../laws/BinderIndexFindsItems.bend as L1
import ./lemmas/BinderIndex.bend as M2
import ./lemmas/BinderIndexIsContains.bend as M3

# the binder's resolution (laws/BinderResolvesInnermostFirst.bend)
# ------------------------------------

# the innermost binder, one binder further out: the one here when it has the
# name, else the one the rest has
law rs.find.arm:
  for +b: Bool
  for +bb: Bind.Bind
  for -found: Maybe<&2, Bind.Bind>
  for -all: List<&2, Bind.Bind>
  for ih: {found == List.head(&2, Bind.Bind, all) : Maybe<&2, Bind.Bind>}
  {Bool.pick(Maybe<&2, Bind.Bind>, b, Some{bb}, found)
    == List.head(&2, Bind.Bind, Bool.pick(List<&2, Bind.Bind>, b, bb <> all, all)) : Maybe<&2, Bind.Bind>}

def rs.find.arm(b, _bb, _found, _all, ih):
  match b:
    case True{}:
      {==}
    case False{}:
      ih

# the binder's search finds the first binder of the name
law rs.find:
  for +env: List<&2, Bind.Bind>
  for +name: String
  {Bind.find(env, name) == List.head(&2, Bind.Bind, Laws.res.all(env, name)) : Maybe<&2, Bind.Bind>}

def rs.find(env, name):
  match env:
    case Nil{}:
      {==}
    case Con{Bind.Bind{+n, +l, +c, +k, +note}, +t}:
      %Equal.sym(Maybe<&2, Bind.Bind>, Bind.find(Bind.Bind{n, l, c, k, note} <> t, name),
        Bool.pick(Maybe<&2, Bind.Bind>, String.eq(n, name), Some{Bind.Bind{n, l, c, k, note}}, Bind.find(t, name)),
        CS.cs.find(n, l, c, k, note, t, name)) :
        {_ == List.head(&2, Bind.Bind, Laws.res.all(Bind.Bind{n, l, c, k, note} <> t, name)) : Maybe<&2, Bind.Bind>}
      rs.find.arm(String.eq(n, name), Bind.Bind{n, l, c, k, note}, Bind.find(t, name), Laws.res.all(t, name),
        rs.find(t, name))

# is there a part after a dot?
def rs.ok(mm: Maybe<&2, String>) -> Bool:
  match mm:
    case None{}:
      False{}
    case Some{_r}:
      True{}

# the part after a dot, "" when there is none
def rs.dflt(mm: Maybe<&2, String>) -> String:
  match mm:
    case None{}:
      ""
    case Some{r}:
      r

# any text starts with the empty text
law rs.starts:
  for +t: String
  {String.starts_with(t, SNil{}) == True{} : Bool}

def rs.starts(t):
  match t:
    case SNil{}:
      {==}
    case SCon{_h, _r}:
      {==}

# a dot, one char further in: here, or wherever the rest has one
law rs.dot.arm:
  for +b: Bool
  for +t: String
  for ih: {String.contains(t, ".") == rs.ok(Laws.res.after(t)) : Bool}
  {String.contains.if(t, ".", String.starts_with.go.if(SNil{}, t, b))
    == rs.ok(Bool.pick(Maybe<&2, String>, b, Some{t}, Laws.res.after(t))) : Bool}

def rs.dot.arm(b, t, ih):
  match b:
    case True{}:
      %Equal.sym(Bool, String.starts_with(t, SNil{}), True{}, rs.starts(t))
        : {String.contains.if(t, ".", _) == True{} : Bool}
      {==}
    case False{}:
      ih

# a name holds a dot exactly when it has a part after one
law rs.dot:
  for +s: String
  {String.contains(s, ".") == rs.ok(Laws.res.after(s)) : Bool}

def rs.dot(s):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      rs.dot.arm(Char.is_eq(h, '.'), t, rs.dot(t))

# the part before a dot, one char further in
law rs.head.arm:
  for +b: Bool
  for +h: Char
  for +t: String
  for ih: {Bind.head_of(String.to_list(t)) == Laws.res.before(t) : String}
  {String.from_list(Lazy.stop(List<&2, Char>, b, Nil{}, _u => h <> Bind.head_of.go(String.to_list(t))))
    == Bool.pick(String, b, SNil{}, SCon{h, Laws.res.before(t)}) : String}

def rs.head.arm(b, h, t, ih):
  match b:
    case True{}:
      {==}
    case False{}:
      Equal.cong(String, String, x => SCon{h, x}, Bind.head_of(String.to_list(t)), Laws.res.before(t), ih)

# the binder's qualifier is the part before the first dot
law rs.head:
  for +s: String
  {Bind.head_of(String.to_list(s)) == Laws.res.before(s) : String}

def rs.head(s):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      rs.head.arm(Char.is_eq(h, '.'), h, t, rs.head(t))

# the part after a dot, one char further in
law rs.rest.arm:
  for +b: Bool
  for +t: String
  for ih: {Bind.rest_of(String.to_list(t)) == rs.dflt(Laws.res.after(t)) : String}
  {Lazy.stop(String, b, String.from_list(String.to_list(t)), _u => Bind.rest_of(String.to_list(t)))
    == rs.dflt(Bool.pick(Maybe<&2, String>, b, Some{t}, Laws.res.after(t))) : String}

def rs.rest.arm(b, t, ih):
  match b:
    case True{}:
      M1.chars(t)
    case False{}:
      ih

# the binder's qualified name is the part after the first dot
law rs.rest:
  for +s: String
  {Bind.rest_of(String.to_list(s)) == rs.dflt(Laws.res.after(s)) : String}

def rs.rest(s):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      rs.rest.arm(Char.is_eq(h, '.'), t, rs.rest(t))

# an alias qualifier, once the name is known to have a dot
law rs.alias:
  for +c: Bool
  for +q: String
  for +r: String
  {Lazy.stop(Bind.Target, Bool.not(c), Bind.TFree{}, _u => Bind.TQual{q, r})
    == Bool.pick(Bind.Target, c, Bind.TQual{q, r}, Bind.TFree{}) : Bind.Target}

def rs.alias(c, _q, _r):
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

# the binder's alias test, by whether the name has a part after a dot
law rs.qual:
  for +mm: Maybe<&2, String>
  for +q: String
  for +als: List<&2, String>
  {Lazy.stop(Bind.Target, Bool.not(Bool.and(rs.ok(mm), Bind.has(als, q))), Bind.TFree{},
      _u => Bind.TQual{q, rs.dflt(mm)})
    == Laws.res.qual(mm, q, als) : Bind.Target}

def rs.qual(mm, q, als):
  match mm:
    case None{}:
      {==}
    case Some{+r}:
      rs.alias(Bind.has(als, q), q, r)

# the binder's alias test, from what it computes of a name: whether it has a
# dot (c) and its part after one (r)
law rs.qual.at:
  for +c: Bool
  for +q: String
  for +r: String
  for +mm: Maybe<&2, String>
  for +als: List<&2, String>
  for e1: {c == rs.ok(mm) : Bool}
  for e2: {r == rs.dflt(mm) : String}
  {Lazy.stop(Bind.Target, Bool.not(Bool.and(c, Bind.has(als, q))), Bind.TFree{}, _u => Bind.TQual{q, r})
    == Laws.res.qual(mm, q, als) : Bind.Target}

def rs.qual.at(c, q, r, mm, als, e1, e2):
  %Equal.sym(Bool, c, rs.ok(mm), e1) : {Lazy.stop(Bind.Target, Bool.not(Bool.and(_, Bind.has(als, q))), Bind.TFree{},
      _u => Bind.TQual{q, r}) == Laws.res.qual(mm, q, als) : Bind.Target}
  %Equal.sym(String, r, rs.dflt(mm), e2) : {Lazy.stop(Bind.Target, Bool.not(Bool.and(rs.ok(mm), Bind.has(als, q))),
      Bind.TFree{}, _u => Bind.TQual{q, _}) == Laws.res.qual(mm, q, als) : Bind.Target}
  rs.qual(mm, q, als)

# what the binder makes of a name no binder holds and no item has
def rs.code(+name: String, als: List<&2, String>) -> Bind.Target:
  +cs = String.to_list(name)
  +head = Bind.head_of(cs)
  Lazy.stop(Bind.Target, Bool.not(Bool.and(String.contains(name, "."), Bind.has(als, head))), Bind.TFree{},
    _u => Bind.TQual{head, Bind.rest_of(cs)})

# a name no binder holds: an item, else what its dot and alias make of it
law rs.none:
  for +name: String
  for +its: List<&2, String>
  for +als: List<&2, String>
  {Bind.resolve.local(None{}, name, Bind.Names{its, als, Bind.index(its)})
    == Laws.res.found(None{}, name, its, als) : Bind.Target}

def rs.none(name, its, als):
  %M3.ic.indexed(its, name) : {Bind.resolve.local(None{}, name, Bind.Names{its, als, Bind.index(its)})
    == Bool.pick(Bind.Target, _, Bind.TItem{name}, Laws.res.qual(Laws.res.after(name), Laws.res.before(name), als))
    : Bind.Target}
  Equal.cong(Bind.Target, Bind.Target,
    x => Bool.pick(Bind.Target, Bind.indexed(Bind.index(its), name), Bind.TItem{name}, x),
    rs.code(name, als),
    Laws.res.qual(Laws.res.after(name), Laws.res.before(name), als),
    Equal.trans(Bind.Target,
      rs.code(name, als),
      Laws.res.qual(Laws.res.after(name), Bind.head_of(String.to_list(name)), als),
      Laws.res.qual(Laws.res.after(name), Laws.res.before(name), als),
      rs.qual.at(String.contains(name, "."), Bind.head_of(String.to_list(name)), Bind.rest_of(String.to_list(name)),
        Laws.res.after(name), als, rs.dot(name), rs.rest(name)),
      Equal.cong(String, Bind.Target, y => Laws.res.qual(Laws.res.after(name), y, als),
        Bind.head_of(String.to_list(name)), Laws.res.before(name), rs.head(name))))

# whatever the search found, the binder and the spec make the same of it
law rs.local:
  for +mm: Maybe<&2, Bind.Bind>
  for +name: String
  for +its: List<&2, String>
  for +als: List<&2, String>
  {Bind.resolve.local(mm, name, Bind.Names{its, als, Bind.index(its)}) == Laws.res.found(mm, name, its, als)
    : Bind.Target}

def rs.local(mm, name, its, als):
  match mm:
    case Some{Bind.Bind{_n, _l, _c, _k, _note}}:
      {==}
    case None{}:
      rs.none(name, its, als)

def Laws.resolves(env, name, its, als):
  %Equal.sym(Maybe<&2, Bind.Bind>, Bind.find(env, name), List.head(&2, Bind.Bind, Laws.res.all(env, name)),
      rs.find(env, name))
    : {Bind.resolve.local(_, name, Bind.Names{its, als, Bind.index(its)}) == Laws.res.spec(env, name, its, als)
      : Bind.Target}
  rs.local(List.head(&2, Bind.Bind, Laws.res.all(env, name)), name, its, als)

def Laws.uses(name, line, col, env, its, als, binds, us, scopes):
  Equal.cong(Bind.Target, Bind.W,
    x => Bind.W{env, Bind.Out{binds, Bind.Use{name, line, col, x} <> us, scopes}},
    Bind.resolve(env, name, Bind.Names{its, als, Bind.index(its)}), Laws.res.spec(env, name, its, als),
    Laws.resolves(env, name, its, als))

# the environment the walk threads (laws/BinderResolvesInnermostFirst.bend)
# ---------------------------------------------

def Laws.restores(kk, kids, body, rest, env, ns, out, e):
  match kk:
    case Tree.SDef{}:
      +h = Bind.walk(kids, Bind.MHead{}, env, ns, out)
      (Bind.out_of(Bind.walk(body, Bind.MBlock{}, Bind.env_of(h), ns,
        Bind.mark(Tree.line(kids), Bind.env_of(h), Bind.out_of(h)))), {==})
    case Tree.SType{}:
      +h = Bind.walk(kids, Bind.MHead{}, env, ns, out)
      (Bind.out_of(Bind.walk(body, Bind.MCtors{}, Bind.env_of(h), ns, Bind.out_of(h))), {==})
    case Tree.SLaw{}:
      +h = Bind.walk(kids, Bind.MHead{}, env, ns, out)
      (Bind.out_of(Bind.walk(body, Bind.MBlock{}, Bind.env_of(h), ns, Bind.out_of(h))), {==})
    case Tree.SImport{}:
      +h = Bind.walk(kids, Bind.MStop{}, env, ns, out)
      (Bind.out_of(Bind.walk(body, Bind.MStop{}, Bind.env_of(h), ns, Bind.out_of(h))), {==})
    case Tree.SCase{}:
      +p = Bind.walk(kids, Bind.MLhs{env, Bind.KPat{}}, env, ns, Bind.mark(Tree.line(kids), env, out))
      (Bind.out_of(Bind.walk(body, Bind.MBlock{}, Bind.env_of(p), ns, Bind.out_of(p))), {==})
    case Tree.SFor{}:
      Empty.absurd(&o: Bind.Out
        -> {Bind.walk(Tree.NCons{Tree.Stmt{Tree.SFor{}, kids, body}, rest}, Bind.MBlock{}, env, ns, out)
          == Bind.walk(rest, Bind.MBlock{}, env, ns, o) : Bind.W}, M1.false_true(e))
    case Tree.SLet{}:
      Empty.absurd(&o: Bind.Out
        -> {Bind.walk(Tree.NCons{Tree.Stmt{Tree.SLet{}, kids, body}, rest}, Bind.MBlock{}, env, ns, out)
          == Bind.walk(rest, Bind.MBlock{}, env, ns, o) : Bind.W}, M1.false_true(e))
    case Tree.STerm{}:
      +t = Bind.walk(kids, Bind.MTerm{}, env, ns, Bind.mark(Tree.line(kids), env, out))
      (Bind.out_of(Bind.walk(body, Bind.MBlock{}, Bind.env_of(t), ns, Bind.out_of(t))), {==})

def Laws.groups(open, gkids, _close, _rest, env, ns, out):
  match open:
    case Lex.Tok{_k, _t, _l, _c}:
      (Bind.out_of(Bind.walk(gkids, Bind.MTerm{}, env, ns, out)), {==})

# the environment big is small with binders put in front
def rs.Ext(big: List<&2, Bind.Bind>, small: List<&2, Bind.Bind>) -> Type:
  &x: List<&2, Bind.Bind> -> {big == List.append(&2, Bind.Bind, x, small) : List<&2, Bind.Bind>}

# appending binders is associative
law rs.app:
  for +a: List<&2, Bind.Bind>
  for +b: List<&2, Bind.Bind>
  for +c: List<&2, Bind.Bind>
  {List.append(&2, Bind.Bind, List.append(&2, Bind.Bind, a, b), c)
    == List.append(&2, Bind.Bind, a, List.append(&2, Bind.Bind, b, c)) : List<&2, Bind.Bind>}

def rs.app(a, b, c):
  match a:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Equal.cong(List<&2, Bind.Bind>, List<&2, Bind.Bind>, x => h <> x,
        List.append(&2, Bind.Bind, List.append(&2, Bind.Bind, t, b), c),
        List.append(&2, Bind.Bind, t, List.append(&2, Bind.Bind, b, c)), rs.app(t, b, c))

# binders in front of binders in front of an environment are binders in front
# of it
law rs.chain:
  for +env: List<&2, Bind.Bind>
  for +env1: List<&2, Bind.Bind>
  for +env2: List<&2, Bind.Bind>
  for w1: rs.Ext(env1, env)
  for w2: rs.Ext(env2, env1)
  rs.Ext(env2, env)

def rs.chain(env, env1, env2, w1, w2):
  (x1, e1) = w1
  (x2, e2) = w2
  +a = {x1 : List<&2, Bind.Bind>}
  +b = {x2 : List<&2, Bind.Bind>}
  (List.append(&2, Bind.Bind, b, a),
    Equal.trans(List<&2, Bind.Bind>, env2, List.append(&2, Bind.Bind, b, env1),
      List.append(&2, Bind.Bind, List.append(&2, Bind.Bind, b, a), env), e2,
      Equal.trans(List<&2, Bind.Bind>, List.append(&2, Bind.Bind, b, env1),
        List.append(&2, Bind.Bind, b, List.append(&2, Bind.Bind, a, env)),
        List.append(&2, Bind.Bind, List.append(&2, Bind.Bind, b, a), env),
        Equal.cong(List<&2, Bind.Bind>, List<&2, Bind.Bind>, y => List.append(&2, Bind.Bind, b, y),
          env1, List.append(&2, Bind.Bind, a, env), e1),
        Equal.sym(List<&2, Bind.Bind>, List.append(&2, Bind.Bind, List.append(&2, Bind.Bind, b, a), env),
          List.append(&2, Bind.Bind, b, List.append(&2, Bind.Bind, a, env)), rs.app(b, a, env)))))

# no binder in front
law rs.same:
  for +env: List<&2, Bind.Bind>
  rs.Ext(env, env)

def rs.same(_env):
  ([], {==})

# after a leaf: at a let's `=` the walk hands back the environment it had;
# anything else it read the rest with, the leaf's binder in front when it
# pushed one
law rs.leaf:
  for +kp: Bool
  for +ou: List<&2, Bind.Bind>
  for +ps: Bool
  for +bb: Bind.Bind
  for +env: List<&2, Bind.Bind>
  for +x: List<&2, Bind.Bind>
  rs.Ext(x, Bind.plan.enter(kp, ou, ps, bb, env)) -> rs.Ext(Bool.pick(List<&2, Bind.Bind>, kp, env, x), env)

def rs.leaf(kp, _ou, ps, bb, env, x):
  match kp:
    case True{}:
      _ih => rs.same(env)
    case False{}:
      match ps:
        case True{}:
          ih => rs.chain(env, bb <> env, x, ([bb], {==}), ih)
        case False{}:
          ih => ih

# the environment after a group or a statement's header, when it is kept
law rs.kept:
  for +b: Bool
  for +x: List<&2, Bind.Bind>
  for +env: List<&2, Bind.Bind>
  rs.Ext(x, env) -> rs.Ext(Bool.pick(List<&2, Bind.Bind>, b, x, env), env)

def rs.kept(b, _x, env):
  match b:
    case True{}:
      w => w
    case False{}:
      _w => rs.same(env)

# the environment after a statement's header, unless it closes its scope
law rs.scoped:
  for +b: Bool
  for +x: List<&2, Bind.Bind>
  for +env: List<&2, Bind.Bind>
  rs.Ext(x, env) -> rs.Ext(Bool.pick(List<&2, Bind.Bind>, b, env, x), env)

def rs.scoped(b, _x, env):
  match b:
    case True{}:
      _w => rs.same(env)
    case False{}:
      w => w

def Laws.extends(nn, mode, env, ns, out):
  match nn:
    case Tree.NCons{hd, +rest}:
      match hd:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{+k, +t, +l, +c}:
              +keep = Bind.plan.keep(mode, k)
              +bb = Bind.plan.binder(mode, k, t, l, c, rest)
              +o1 = Bind.plan.recorded(Bind.plan.rec(mode, k, rest), bb, out)
              +o2 = Bind.plan.used(Bind.plan.use(mode, k, rest), t, l, c, env, ns, o1)
              +ps = Bind.plan.push(mode, k, rest)
              +ou = Bind.plan.outer(mode)
              +e2 = Bind.plan.enter(keep, ou, ps, bb, env)
              +r = Bind.walk(rest, Bind.plan.after(mode, k, t, rest), e2, ns, o2)
              rs.leaf(keep, ou, ps, bb, env, Bind.env_of(r))(
                Laws.extends(rest, Bind.plan.after(mode, k, t, rest), e2, ns, o2))
        case Tree.Group{open, gkids, _close}:
          match open:
            case Lex.Tok{_gk, +gt, _gl, _gc}:
              +g = Bind.walk(gkids, Bind.plan.ginner(mode, gt), env, ns, out)
              +e2 = Bool.pick(List<&2, Bind.Bind>, Bind.plan.gkeeps(mode), Bind.env_of(g), env)
              rs.chain(env, e2, Bind.env_of(Bind.walk(rest, Bind.plan.gnext(mode), e2, ns, Bind.out_of(g))),
                rs.kept(Bind.plan.gkeeps(mode), Bind.env_of(g), env)(
                  Laws.extends(gkids, Bind.plan.ginner(mode, gt), env, ns, out)),
                Laws.extends(rest, Bind.plan.gnext(mode), e2, ns, Bind.out_of(g)))
        case Tree.Stmt{+sk, +kids, body}:
          +o1 = Bind.plan.marked(Bind.plan.mark_head(mode, sk), Tree.line(kids), env, out)
          +h = Bind.walk(kids, Bind.plan.kmode(mode, sk, env), env, ns, o1)
          +b = Bind.walk(body, Bind.plan.bmode(mode, sk), Bind.env_of(h), ns,
            Bind.plan.marked(Bind.plan.mark_body(mode, sk), Tree.line(kids), Bind.env_of(h), Bind.out_of(h)))
          +e3 = Bool.pick(List<&2, Bind.Bind>, Bind.plan.scoped(mode, sk), env, Bind.env_of(h))
          rs.chain(env, e3, Bind.env_of(Bind.walk(rest, Bind.plan.snext(mode), e3, ns, Bind.out_of(b))),
            rs.scoped(Bind.plan.scoped(mode, sk), Bind.env_of(h), env)(
              Laws.extends(kids, Bind.plan.kmode(mode, sk, env), env, ns, o1)),
            Laws.extends(rest, Bind.plan.snext(mode), e3, ns, Bind.out_of(b)))
        case Tree.NNil{}:
          Laws.extends(rest, Bind.plan.skip(mode), env, ns, out)
        case Tree.NCons{_a, _b}:
          Laws.extends(rest, Bind.plan.skip(mode), env, ns, out)
    case Tree.NNil{}:
      rs.same(env)
    case Tree.Leaf{_tok}:
      rs.same(env)
    case Tree.Group{_o, _g, _cl}:
      rs.same(env)
    case Tree.Stmt{_sk, _kids, _body}:
      rs.same(env)

# binders in front, one binder further in: the one here when it has the name
law rs.shadows.arm:
  for +b: Bool
  for +bb: Bind.Bind
  for -front: List<&2, Bind.Bind>
  for -all: List<&2, Bind.Bind>
  for +behind: Maybe<&2, Bind.Bind>
  for ih: {List.head(&2, Bind.Bind, all) == Laws.res.first(List.head(&2, Bind.Bind, front), behind)
    : Maybe<&2, Bind.Bind>}
  {List.head(&2, Bind.Bind, Bool.pick(List<&2, Bind.Bind>, b, bb <> all, all))
    == Laws.res.first(List.head(&2, Bind.Bind, Bool.pick(List<&2, Bind.Bind>, b, bb <> front, front)), behind)
    : Maybe<&2, Bind.Bind>}

def rs.shadows.arm(b, _bb, _front, _all, _behind, ih):
  match b:
    case True{}:
      {==}
    case False{}:
      ih

def Laws.shadows(ext, env, name):
  match ext:
    case Nil{}:
      {==}
    case Con{Bind.Bind{+n, +l, +c, +k, +note}, +t}:
      rs.shadows.arm(String.eq(n, name), Bind.Bind{n, l, c, k, note}, Laws.res.all(t, name),
        Laws.res.all(List.append(&2, Bind.Bind, t, env), name), List.head(&2, Bind.Bind, Laws.res.all(env, name)),
        Laws.shadows(t, env, name))

# a let's or a `for`'s header, as binders in front, carried to what follows
law rs.lets.arm:
  for +rest: Tree.Node
  for +env: List<&2, Bind.Bind>
  for +ns: Bind.Names
  for +hv: List<&2, Bind.Bind>
  for +o: Bind.Out
  for w: rs.Ext(hv, env)
  exs ext: List<&2, Bind.Bind>
  exs o2: Bind.Out
  {Bind.walk(rest, Bind.MBlock{}, hv, ns, o)
    == Bind.walk(rest, Bind.MBlock{}, List.append(&2, Bind.Bind, ext, env), ns, o2) : Bind.W}

def rs.lets.arm(rest, env, ns, hv, o, w):
  (x, e) = w
  +xs = {x : List<&2, Bind.Bind>}
  (xs, o, Equal.cong(List<&2, Bind.Bind>, Bind.W, y => Bind.walk(rest, Bind.MBlock{}, y, ns, o),
    hv, List.append(&2, Bind.Bind, xs, env), e))

# what `lets` claims of a statement of kind kk
def rs.lets.ty(
  kk: Tree.StmtKind,
  kids: Tree.Node,
  body: Tree.Node,
  +rest: Tree.Node,
  +env: List<&2, Bind.Bind>,
  +ns: Bind.Names,
  out: Bind.Out
) -> Type:
  (&ext: List<&2, Bind.Bind> -> &o: Bind.Out
    -> {Bind.walk(Tree.NCons{Tree.Stmt{kk, kids, body}, rest}, Bind.MBlock{}, env, ns, out)
      == Bind.walk(rest, Bind.MBlock{}, List.append(&2, Bind.Bind, ext, env), ns, o) : Bind.W})

def Laws.lets(kk, kids, body, rest, env, ns, out, e):
  match kk:
    case Tree.SFor{}:
      +o1 = Bind.mark(Tree.line(kids), env, out)
      +h = Bind.walk(kids, Bind.MLhs{env, Bind.KFor{}}, env, ns, o1)
      rs.lets.arm(rest, env, ns, Bind.env_of(h),
        Bind.out_of(Bind.walk(body, Bind.MBlock{}, Bind.env_of(h), ns, Bind.out_of(h))),
        Laws.extends(kids, Bind.MLhs{env, Bind.KFor{}}, env, ns, o1))
    case Tree.SLet{}:
      +o1 = Bind.mark(Tree.line(kids), env, out)
      +h = Bind.walk(kids, Bind.MLhs{env, Bind.KLocal{}}, env, ns, o1)
      rs.lets.arm(rest, env, ns, Bind.env_of(h),
        Bind.out_of(Bind.walk(body, Bind.MBlock{}, Bind.env_of(h), ns, Bind.out_of(h))),
        Laws.extends(kids, Bind.MLhs{env, Bind.KLocal{}}, env, ns, o1))
    case Tree.SDef{}:
      Empty.absurd(rs.lets.ty(Tree.SDef{}, kids, body, rest, env, ns, out), M1.true_false(e))
    case Tree.SType{}:
      Empty.absurd(rs.lets.ty(Tree.SType{}, kids, body, rest, env, ns, out), M1.true_false(e))
    case Tree.SLaw{}:
      Empty.absurd(rs.lets.ty(Tree.SLaw{}, kids, body, rest, env, ns, out), M1.true_false(e))
    case Tree.SImport{}:
      Empty.absurd(rs.lets.ty(Tree.SImport{}, kids, body, rest, env, ns, out), M1.true_false(e))
    case Tree.SCase{}:
      Empty.absurd(rs.lets.ty(Tree.SCase{}, kids, body, rest, env, ns, out), M1.true_false(e))
    case Tree.STerm{}:
      Empty.absurd(rs.lets.ty(Tree.STerm{}, kids, body, rest, env, ns, out), M1.true_false(e))
