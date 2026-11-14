# The lines under a let are read by what the let's own line ends in. Bend's
# blocks are layout-free and the tree puts every deeper line under the line
# above it, so under a let in a block they are one of three things. When the
# let's line ends in `=` or `<-`, they are its value, and they see the names
# outside the let, as a right side on one line does: `st =` then
# `step(st)` reads the old st, never the one being bound. When it ends in
# `=>`, they are the body of the lambda that is its value, and they see the
# names outside the let and the lambda's parameters (what the let's line
# leaves in scope when it is read as a term). Otherwise they are the next
# statements and see the let's names, as before, and so do the lines under
# every other statement. Whatever is under it, the statements after a let
# are read with the let's names (laws/BinderResolvesInnermostFirst.bend's
# `lets`). Internal behavior of src/syntax/bind.bend, not interface.
#
# also rests on: laws/BinderResolvesInnermostFirst.bend
import Base
import ../src/syntax/lex.bend as Lex
import ../src/syntax/tree.bend as Tree
import ../src/syntax/bind.bend as Bind
import ./defs/TokenKinds.bend as D1
import ./defs/Chains.bend as D2

# is the statement a let? Law vocabulary: bolt never calls it
def under.is_let(sk: Tree.StmtKind) -> Bool:
  match sk:
    case Tree.SLet{}:
      True{}
    case _other:
      False{}

# LAW: a chain's last token is its one node when that is a leaf
law last_of_one_leaf:
  for kk: Lex.TokKind
  for tt: String
  for ll: U32
  for cc: U32
  {Bind.plan.last(Tree.NCons{Tree.Leaf{Lex.Tok{kk, tt, ll, cc}}, Tree.NNil{}}) == kk : Lex.TokKind}

# LAW: and the last token of the rest when more nodes follow the first
law last_of_a_longer_chain:
  for hh: Tree.Node
  for h2: Tree.Node
  for rest: Tree.Node
  {Bind.plan.last(Tree.NCons{hh, Tree.NCons{h2, rest}}) == Bind.plan.last(Tree.NCons{h2, rest}) : Lex.TokKind}

# LAW: under a let whose line ends in `=` or `<-`, the lines are its value
law value_under_eq_or_bind:
  for kids: Tree.Node
  for hh: Tree.Node
  for tt: Tree.Node
  for e: {D1.kinds.among(Bind.plan.last(kids), [Lex.TEq{}, Lex.TBind{}]) == True{} : Bool}
  {Bind.plan.wraps(Bind.MBlock{}, Tree.SLet{}, kids, Tree.NCons{hh, tt}) == Bind.UValue{} : Bind.Under}

# LAW: under a let whose line ends in `=>`, they are a lambda's body
law lambda_under_lam:
  for kids: Tree.Node
  for hh: Tree.Node
  for tt: Tree.Node
  for e: {D1.kinds.among(Bind.plan.last(kids), [Lex.TLam{}]) == True{} : Bool}
  {Bind.plan.wraps(Bind.MBlock{}, Tree.SLet{}, kids, Tree.NCons{hh, tt}) == Bind.ULambda{} : Bind.Under}

# LAW: under a let whose line ends in anything else, they are the next
# statements
law next_under_a_finished_let:
  for kids: Tree.Node
  for hh: Tree.Node
  for tt: Tree.Node
  for e: {D1.kinds.among(Bind.plan.last(kids), [Lex.TEq{}, Lex.TBind{}, Lex.TLam{}]) == False{} : Bool}
  {Bind.plan.wraps(Bind.MBlock{}, Tree.SLet{}, kids, Tree.NCons{hh, tt}) == Bind.UNext{} : Bind.Under}

# LAW: a let with no line under it asks nothing of its last token
law nothing_under_a_let:
  for kids: Tree.Node
  for body: Tree.Node
  for e: {D2.chains.is_cons(body) == False{} : Bool}
  {Bind.plan.wraps(Bind.MBlock{}, Tree.SLet{}, kids, body) == Bind.UNext{} : Bind.Under}

# LAW: under any statement that is no let, in a block, the lines are the
# next statements
law next_under_other_statements:
  for sk: Tree.StmtKind
  for kids: Tree.Node
  for body: Tree.Node
  for e: {under.is_let(sk) == False{} : Bool}
  {Bind.plan.wraps(Bind.MBlock{}, sk, kids, body) == Bind.UNext{} : Bind.Under}

# LAW: a let's value under it is walked with the environment the let was
# entered with, and the statements after the let with the let's names
law value_sees_the_outer_names:
  for +kids: Tree.Node
  for +body: Tree.Node
  for +rest: Tree.Node
  for +env: List<&2, Bind.Bind>
  for +ns: Bind.Names
  for +out: Bind.Out
  for e: {Bind.plan.wraps(Bind.MBlock{}, Tree.SLet{}, kids, body) == Bind.UValue{} : Bind.Under}
  {Bind.walk(Tree.NCons{Tree.Stmt{Tree.SLet{}, kids, body}, rest}, Bind.MBlock{}, env, ns, out)
    == Bind.walk(rest, Bind.MBlock{},
      Bind.env_of(Bind.walk(kids, Bind.MLhs{env, Bind.KLocal{}}, env, ns, Bind.mark(Tree.line(kids), env, out))),
      ns,
      Bind.out_of(Bind.walk(body, Bind.MBlock{}, env, ns,
        Bind.out_of(Bind.walk(kids, Bind.MLhs{env, Bind.KLocal{}}, env, ns, Bind.mark(Tree.line(kids), env, out))))))
    : Bind.W}

# LAW: a lambda's body under a let is walked with what the let's own line
# leaves in scope when it is read as a term from the environment the let was
# entered with: the names outside the let, the lambda's parameters in front
law lambda_body_sees_its_parameters:
  for +kids: Tree.Node
  for +body: Tree.Node
  for +rest: Tree.Node
  for +env: List<&2, Bind.Bind>
  for +ns: Bind.Names
  for +out: Bind.Out
  for e: {Bind.plan.wraps(Bind.MBlock{}, Tree.SLet{}, kids, body) == Bind.ULambda{} : Bind.Under}
  {Bind.walk(Tree.NCons{Tree.Stmt{Tree.SLet{}, kids, body}, rest}, Bind.MBlock{}, env, ns, out)
    == Bind.walk(rest, Bind.MBlock{},
      Bind.env_of(Bind.walk(kids, Bind.MLhs{env, Bind.KLocal{}}, env, ns, Bind.mark(Tree.line(kids), env, out))),
      ns,
      Bind.out_of(Bind.walk(body, Bind.MBlock{},
        Bind.env_of(Bind.walk(kids, Bind.MTerm{}, env, ns, Bind.Out{[], [], []})), ns,
        Bind.out_of(Bind.walk(kids, Bind.MLhs{env, Bind.KLocal{}}, env, ns, Bind.mark(Tree.line(kids), env, out))))))
    : Bind.W}

# LAW: the next statements under a let are walked with the let's names, as
# before
law next_statements_see_the_let:
  for +kids: Tree.Node
  for +body: Tree.Node
  for +rest: Tree.Node
  for +env: List<&2, Bind.Bind>
  for +ns: Bind.Names
  for +out: Bind.Out
  for e: {Bind.plan.wraps(Bind.MBlock{}, Tree.SLet{}, kids, body) == Bind.UNext{} : Bind.Under}
  {Bind.walk(Tree.NCons{Tree.Stmt{Tree.SLet{}, kids, body}, rest}, Bind.MBlock{}, env, ns, out)
    == Bind.walk(rest, Bind.MBlock{},
      Bind.env_of(Bind.walk(kids, Bind.MLhs{env, Bind.KLocal{}}, env, ns, Bind.mark(Tree.line(kids), env, out))),
      ns,
      Bind.out_of(Bind.walk(body, Bind.MBlock{},
        Bind.env_of(Bind.walk(kids, Bind.MLhs{env, Bind.KLocal{}}, env, ns, Bind.mark(Tree.line(kids), env, out))),
        ns,
        Bind.out_of(Bind.walk(kids, Bind.MLhs{env, Bind.KLocal{}}, env, ns, Bind.mark(Tree.line(kids), env, out))))))
    : Bind.W}

# LAW: `x =` with `y` on the line under it: y is resolved against the names
# outside the let, x's binder not among them, whatever the names, the
# positions, the scope and the output so far
law name_under_a_let_is_not_the_let:
  for +xt: String
  for +xl: U32
  for +xc: U32
  for +et: String
  for +el: U32
  for +ec: U32
  for +yt: String
  for +yl: U32
  for +yc: U32
  for +env: List<&2, Bind.Bind>
  for +ns: Bind.Names
  for +binds: List<&2, Bind.Bind>
  for +uses: List<&2, Bind.Use>
  for +scopes: List<&2, Bind.Scope>
  {Bind.walk(
    Tree.NCons{Tree.Stmt{Tree.SLet{},
      Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, xt, xl, xc}},
        Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TEq{}, et, el, ec}}, Tree.NNil{}}},
      Tree.NCons{Tree.Stmt{Tree.STerm{},
        Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, yt, yl, yc}}, Tree.NNil{}}, Tree.NNil{}}, Tree.NNil{}}},
      Tree.NNil{}},
    Bind.MBlock{}, env, ns, Bind.Out{binds, uses, scopes})
    == Bind.W{Bind.Bind{xt, xl, xc, Bind.KLocal{}, ""} <> env,
      Bind.Out{Bind.Bind{xt, xl, xc, Bind.KLocal{}, ""} <> binds,
        Bind.Use{yt, yl, yc, Bind.resolve(env, yt, ns)} <> uses,
        Bind.Scope{yl, env} <> (Bind.Scope{xl, env} <> scopes)}} : Bind.W}
