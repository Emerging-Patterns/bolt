# proofs of laws/LetReadsTheLinesUnderIt.bend
import Base
import ../laws/LetReadsTheLinesUnderIt.bend as Laws
import ../src/syntax/lex.bend as Lex
import ../src/syntax/tree.bend as Tree
import ../src/syntax/bind.bend as Bind
import ../laws/defs/TokenKinds.bend as D1
import ../laws/defs/Chains.bend as D2
import ./lemmas/BoolEmptiness.bend as MB

def Laws.name_under_a_let_is_not_the_let(
  _xt,
  _xl,
  _xc,
  _et,
  _el,
  _ec,
  _yt,
  _yl,
  _yc,
  _env,
  _ns,
  _binds,
  _uses,
  _scopes
):
  {==}

# a let that ends in `=` or `<-` has its value under it
law by.value:
  for kk: Lex.TokKind
  for e: {D1.kinds.among(kk, [Lex.TEq{}, Lex.TBind{}]) == True{} : Bool}
  {Bind.plan.wraps.by(kk) == Bind.UValue{} : Bind.Under}

def by.value(kk, e):
  match kk:
    case Lex.TName{}:
      Empty.absurd({Bind.plan.wraps.by(Lex.TName{}) == Bind.UValue{} : Bind.Under}, MB.false_true(e))
    case Lex.TUpper{}:
      Empty.absurd({Bind.plan.wraps.by(Lex.TUpper{}) == Bind.UValue{} : Bind.Under}, MB.false_true(e))
    case Lex.TDotted{}:
      Empty.absurd({Bind.plan.wraps.by(Lex.TDotted{}) == Bind.UValue{} : Bind.Under}, MB.false_true(e))
    case Lex.TWild{}:
      Empty.absurd({Bind.plan.wraps.by(Lex.TWild{}) == Bind.UValue{} : Bind.Under}, MB.false_true(e))
    case Lex.TKey{}:
      Empty.absurd({Bind.plan.wraps.by(Lex.TKey{}) == Bind.UValue{} : Bind.Under}, MB.false_true(e))
    case Lex.TNum{}:
      Empty.absurd({Bind.plan.wraps.by(Lex.TNum{}) == Bind.UValue{} : Bind.Under}, MB.false_true(e))
    case Lex.TStr{}:
      Empty.absurd({Bind.plan.wraps.by(Lex.TStr{}) == Bind.UValue{} : Bind.Under}, MB.false_true(e))
    case Lex.TChar{}:
      Empty.absurd({Bind.plan.wraps.by(Lex.TChar{}) == Bind.UValue{} : Bind.Under}, MB.false_true(e))
    case Lex.TComment{}:
      Empty.absurd({Bind.plan.wraps.by(Lex.TComment{}) == Bind.UValue{} : Bind.Under}, MB.false_true(e))
    case Lex.TSpace{}:
      Empty.absurd({Bind.plan.wraps.by(Lex.TSpace{}) == Bind.UValue{} : Bind.Under}, MB.false_true(e))
    case Lex.TNewline{}:
      Empty.absurd({Bind.plan.wraps.by(Lex.TNewline{}) == Bind.UValue{} : Bind.Under}, MB.false_true(e))
    case Lex.TOp{}:
      Empty.absurd({Bind.plan.wraps.by(Lex.TOp{}) == Bind.UValue{} : Bind.Under}, MB.false_true(e))
    case Lex.TColon{}:
      Empty.absurd({Bind.plan.wraps.by(Lex.TColon{}) == Bind.UValue{} : Bind.Under}, MB.false_true(e))
    case Lex.TEq{}:
      {==}
    case Lex.TBind{}:
      {==}
    case Lex.TArrow{}:
      Empty.absurd({Bind.plan.wraps.by(Lex.TArrow{}) == Bind.UValue{} : Bind.Under}, MB.false_true(e))
    case Lex.TLam{}:
      Empty.absurd({Bind.plan.wraps.by(Lex.TLam{}) == Bind.UValue{} : Bind.Under}, MB.false_true(e))
    case Lex.TAll{}:
      Empty.absurd({Bind.plan.wraps.by(Lex.TAll{}) == Bind.UValue{} : Bind.Under}, MB.false_true(e))
    case Lex.TAmp{}:
      Empty.absurd({Bind.plan.wraps.by(Lex.TAmp{}) == Bind.UValue{} : Bind.Under}, MB.false_true(e))
    case Lex.TOpen{}:
      Empty.absurd({Bind.plan.wraps.by(Lex.TOpen{}) == Bind.UValue{} : Bind.Under}, MB.false_true(e))
    case Lex.TClose{}:
      Empty.absurd({Bind.plan.wraps.by(Lex.TClose{}) == Bind.UValue{} : Bind.Under}, MB.false_true(e))
    case Lex.TComma{}:
      Empty.absurd({Bind.plan.wraps.by(Lex.TComma{}) == Bind.UValue{} : Bind.Under}, MB.false_true(e))

# a let that ends in `=>` has a lambda's body under it
law by.lambda:
  for kk: Lex.TokKind
  for e: {D1.kinds.among(kk, [Lex.TLam{}]) == True{} : Bool}
  {Bind.plan.wraps.by(kk) == Bind.ULambda{} : Bind.Under}

def by.lambda(kk, e):
  match kk:
    case Lex.TName{}:
      Empty.absurd({Bind.plan.wraps.by(Lex.TName{}) == Bind.ULambda{} : Bind.Under}, MB.false_true(e))
    case Lex.TUpper{}:
      Empty.absurd({Bind.plan.wraps.by(Lex.TUpper{}) == Bind.ULambda{} : Bind.Under}, MB.false_true(e))
    case Lex.TDotted{}:
      Empty.absurd({Bind.plan.wraps.by(Lex.TDotted{}) == Bind.ULambda{} : Bind.Under}, MB.false_true(e))
    case Lex.TWild{}:
      Empty.absurd({Bind.plan.wraps.by(Lex.TWild{}) == Bind.ULambda{} : Bind.Under}, MB.false_true(e))
    case Lex.TKey{}:
      Empty.absurd({Bind.plan.wraps.by(Lex.TKey{}) == Bind.ULambda{} : Bind.Under}, MB.false_true(e))
    case Lex.TNum{}:
      Empty.absurd({Bind.plan.wraps.by(Lex.TNum{}) == Bind.ULambda{} : Bind.Under}, MB.false_true(e))
    case Lex.TStr{}:
      Empty.absurd({Bind.plan.wraps.by(Lex.TStr{}) == Bind.ULambda{} : Bind.Under}, MB.false_true(e))
    case Lex.TChar{}:
      Empty.absurd({Bind.plan.wraps.by(Lex.TChar{}) == Bind.ULambda{} : Bind.Under}, MB.false_true(e))
    case Lex.TComment{}:
      Empty.absurd({Bind.plan.wraps.by(Lex.TComment{}) == Bind.ULambda{} : Bind.Under}, MB.false_true(e))
    case Lex.TSpace{}:
      Empty.absurd({Bind.plan.wraps.by(Lex.TSpace{}) == Bind.ULambda{} : Bind.Under}, MB.false_true(e))
    case Lex.TNewline{}:
      Empty.absurd({Bind.plan.wraps.by(Lex.TNewline{}) == Bind.ULambda{} : Bind.Under}, MB.false_true(e))
    case Lex.TOp{}:
      Empty.absurd({Bind.plan.wraps.by(Lex.TOp{}) == Bind.ULambda{} : Bind.Under}, MB.false_true(e))
    case Lex.TColon{}:
      Empty.absurd({Bind.plan.wraps.by(Lex.TColon{}) == Bind.ULambda{} : Bind.Under}, MB.false_true(e))
    case Lex.TEq{}:
      Empty.absurd({Bind.plan.wraps.by(Lex.TEq{}) == Bind.ULambda{} : Bind.Under}, MB.false_true(e))
    case Lex.TBind{}:
      Empty.absurd({Bind.plan.wraps.by(Lex.TBind{}) == Bind.ULambda{} : Bind.Under}, MB.false_true(e))
    case Lex.TArrow{}:
      Empty.absurd({Bind.plan.wraps.by(Lex.TArrow{}) == Bind.ULambda{} : Bind.Under}, MB.false_true(e))
    case Lex.TLam{}:
      {==}
    case Lex.TAll{}:
      Empty.absurd({Bind.plan.wraps.by(Lex.TAll{}) == Bind.ULambda{} : Bind.Under}, MB.false_true(e))
    case Lex.TAmp{}:
      Empty.absurd({Bind.plan.wraps.by(Lex.TAmp{}) == Bind.ULambda{} : Bind.Under}, MB.false_true(e))
    case Lex.TOpen{}:
      Empty.absurd({Bind.plan.wraps.by(Lex.TOpen{}) == Bind.ULambda{} : Bind.Under}, MB.false_true(e))
    case Lex.TClose{}:
      Empty.absurd({Bind.plan.wraps.by(Lex.TClose{}) == Bind.ULambda{} : Bind.Under}, MB.false_true(e))
    case Lex.TComma{}:
      Empty.absurd({Bind.plan.wraps.by(Lex.TComma{}) == Bind.ULambda{} : Bind.Under}, MB.false_true(e))

# a let that ends in anything else has the next statements under it
law by.next:
  for kk: Lex.TokKind
  for e: {D1.kinds.among(kk, [Lex.TEq{}, Lex.TBind{}, Lex.TLam{}]) == False{} : Bool}
  {Bind.plan.wraps.by(kk) == Bind.UNext{} : Bind.Under}

def by.next(kk, e):
  match kk:
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
      Empty.absurd({Bind.plan.wraps.by(Lex.TEq{}) == Bind.UNext{} : Bind.Under}, MB.true_false(e))
    case Lex.TBind{}:
      Empty.absurd({Bind.plan.wraps.by(Lex.TBind{}) == Bind.UNext{} : Bind.Under}, MB.true_false(e))
    case Lex.TArrow{}:
      {==}
    case Lex.TLam{}:
      Empty.absurd({Bind.plan.wraps.by(Lex.TLam{}) == Bind.UNext{} : Bind.Under}, MB.true_false(e))
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

def Laws.last_of_one_leaf(_kk, _tt, _ll, _cc):
  {==}

def Laws.last_of_a_longer_chain(hh, _h2, _rest):
  match hh:
    case Tree.Leaf{tok}:
      match tok:
        case Lex.Tok{k, t, l, c}:
          {==}
    case Tree.Group{o, gk, cl}:
      {==}
    case Tree.Stmt{sk, sks, sb}:
      {==}
    case Tree.NNil{}:
      {==}
    case Tree.NCons{x, y}:
      {==}

def Laws.value_under_eq_or_bind(kids, _hh, _tt, e):
  by.value(Bind.plan.last(kids), e)

def Laws.lambda_under_lam(kids, _hh, _tt, e):
  by.lambda(Bind.plan.last(kids), e)

def Laws.next_under_a_finished_let(kids, _hh, _tt, e):
  by.next(Bind.plan.last(kids), e)

def Laws.nothing_under_a_let(kids, body, e):
  match body:
    case Tree.NCons{h, t}:
      Empty.absurd({Bind.plan.wraps(Bind.MBlock{}, Tree.SLet{}, kids, Tree.NCons{h, t}) == Bind.UNext{} : Bind.Under},
        MB.true_false(e))
    case Tree.Leaf{tok}:
      {==}
    case Tree.Group{o, gk, cl}:
      {==}
    case Tree.Stmt{sk, sks, sb}:
      {==}
    case Tree.NNil{}:
      {==}

def Laws.next_under_other_statements(sk, kids, body, e):
  match sk:
    case Tree.SDef{}:
      {==}
    case Tree.SType{}:
      {==}
    case Tree.SLaw{}:
      {==}
    case Tree.SImport{}:
      {==}
    case Tree.SCase{}:
      {==}
    case Tree.SFor{}:
      {==}
    case Tree.SLet{}:
      Empty.absurd({Bind.plan.wraps(Bind.MBlock{}, Tree.SLet{}, kids, body) == Bind.UNext{} : Bind.Under},
        MB.true_false(e))
    case Tree.STerm{}:
      {==}

def Laws.value_sees_the_outer_names(kids, body, rest, env, ns, out, e):
  %Equal.sym(Bind.Under, Bind.plan.wraps(Bind.MBlock{}, Tree.SLet{}, kids, body), Bind.UValue{}, e) :
    {Bind.walk(rest, Bind.MBlock{},
      Bind.env_of(Bind.walk(kids, Bind.MLhs{env, Bind.KLocal{}}, env, ns, Bind.mark(Tree.line(kids), env, out))),
      ns,
      Bind.out_of(Bind.walk(body, Bind.MBlock{},
        Bind.plan.under(_, env,
          Bind.env_of(Bind.walk(kids, Bind.MLhs{env, Bind.KLocal{}}, env, ns, Bind.mark(Tree.line(kids), env, out))),
          _u => Bind.env_of(Bind.walk(kids, Bind.MTerm{}, env, ns, Bind.Out{[], [], []}))),
        ns,
        Bind.out_of(Bind.walk(kids, Bind.MLhs{env, Bind.KLocal{}}, env, ns, Bind.mark(Tree.line(kids), env, out))))))
      == Bind.walk(rest, Bind.MBlock{},
        Bind.env_of(Bind.walk(kids, Bind.MLhs{env, Bind.KLocal{}}, env, ns, Bind.mark(Tree.line(kids), env, out))),
        ns,
        Bind.out_of(Bind.walk(body, Bind.MBlock{},
          env,
          ns,
          Bind.out_of(Bind.walk(kids, Bind.MLhs{env, Bind.KLocal{}}, env, ns, Bind.mark(Tree.line(kids), env, out))))))
      : Bind.W}
  {==}

def Laws.lambda_body_sees_its_parameters(kids, body, rest, env, ns, out, e):
  %Equal.sym(Bind.Under, Bind.plan.wraps(Bind.MBlock{}, Tree.SLet{}, kids, body), Bind.ULambda{}, e) :
    {Bind.walk(rest, Bind.MBlock{},
      Bind.env_of(Bind.walk(kids, Bind.MLhs{env, Bind.KLocal{}}, env, ns, Bind.mark(Tree.line(kids), env, out))),
      ns,
      Bind.out_of(Bind.walk(body, Bind.MBlock{},
        Bind.plan.under(_, env,
          Bind.env_of(Bind.walk(kids, Bind.MLhs{env, Bind.KLocal{}}, env, ns, Bind.mark(Tree.line(kids), env, out))),
          _u => Bind.env_of(Bind.walk(kids, Bind.MTerm{}, env, ns, Bind.Out{[], [], []}))),
        ns,
        Bind.out_of(Bind.walk(kids, Bind.MLhs{env, Bind.KLocal{}}, env, ns, Bind.mark(Tree.line(kids), env, out))))))
      == Bind.walk(rest, Bind.MBlock{},
        Bind.env_of(Bind.walk(kids, Bind.MLhs{env, Bind.KLocal{}}, env, ns, Bind.mark(Tree.line(kids), env, out))),
        ns,
        Bind.out_of(Bind.walk(body, Bind.MBlock{},
          Bind.env_of(Bind.walk(kids, Bind.MTerm{}, env, ns, Bind.Out{[], [], []})),
          ns,
          Bind.out_of(Bind.walk(kids, Bind.MLhs{env, Bind.KLocal{}}, env, ns, Bind.mark(Tree.line(kids), env, out))))))
      : Bind.W}
  {==}

def Laws.next_statements_see_the_let(kids, body, rest, env, ns, out, e):
  %Equal.sym(Bind.Under, Bind.plan.wraps(Bind.MBlock{}, Tree.SLet{}, kids, body), Bind.UNext{}, e) :
    {Bind.walk(rest, Bind.MBlock{},
      Bind.env_of(Bind.walk(kids, Bind.MLhs{env, Bind.KLocal{}}, env, ns, Bind.mark(Tree.line(kids), env, out))),
      ns,
      Bind.out_of(Bind.walk(body, Bind.MBlock{},
        Bind.plan.under(_, env,
          Bind.env_of(Bind.walk(kids, Bind.MLhs{env, Bind.KLocal{}}, env, ns, Bind.mark(Tree.line(kids), env, out))),
          _u => Bind.env_of(Bind.walk(kids, Bind.MTerm{}, env, ns, Bind.Out{[], [], []}))),
        ns,
        Bind.out_of(Bind.walk(kids, Bind.MLhs{env, Bind.KLocal{}}, env, ns, Bind.mark(Tree.line(kids), env, out))))))
      == Bind.walk(rest, Bind.MBlock{},
        Bind.env_of(Bind.walk(kids, Bind.MLhs{env, Bind.KLocal{}}, env, ns, Bind.mark(Tree.line(kids), env, out))),
        ns,
        Bind.out_of(Bind.walk(body, Bind.MBlock{},
          Bind.env_of(Bind.walk(kids, Bind.MLhs{env, Bind.KLocal{}}, env, ns, Bind.mark(Tree.line(kids), env, out))),
          ns,
          Bind.out_of(Bind.walk(kids, Bind.MLhs{env, Bind.KLocal{}}, env, ns, Bind.mark(Tree.line(kids), env, out))))))
      : Bind.W}
  {==}
