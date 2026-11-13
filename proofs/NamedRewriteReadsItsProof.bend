# proofs of laws/NamedRewriteReadsItsProof.bend
import Base
import ../laws/NamedRewriteReadsItsProof.bend as Laws
import ../src/syntax/lex.bend as Lex
import ../src/syntax/tree.bend as Tree
import ../src/syntax/bind.bend as Bind

def Laws.rewrite_uses_its_proof(
  _ol,
  _oc,
  _ht,
  _hl,
  _hc,
  _at,
  _al,
  _ac,
  _et,
  _el,
  _ec,
  _ct,
  _cl,
  _cc,
  _env,
  _ns,
  out
):
  match out:
    case Bind.Out{binds, uses, scopes}:
      {==}

def Laws.arrow_still_binds(_at, _al, _ac, _et, _el, _ec, _ct, _cl, _cc, _env, _ns, _binds, _uses, _scopes):
  {==}

def Laws.rewrite_leads(rest):
  match rest:
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, _t, _l, _c}}, +r}:
      match k:
        case Lex.TName{}:
          match r:
            case Tree.NCons{Tree.Leaf{Lex.Tok{k2, _t2, _l2, _c2}}, _r2}:
              match k2:
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
            case Tree.NCons{Tree.Group{_o, _g, _cl}, _r2}:
              {==}
            case Tree.NCons{Tree.Stmt{_kd, _ks, _b}, _r2}:
              {==}
            case Tree.NCons{Tree.NNil{}, _r2}:
              {==}
            case Tree.NCons{Tree.NCons{_a, _b}, _r2}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.Leaf{_tok}:
              {==}
            case Tree.Group{_o, _g, _cl}:
              {==}
            case Tree.Stmt{_kd, _ks, _b}:
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
    case Tree.NCons{Tree.Group{_o, _g, _cl}, _r}:
      {==}
    case Tree.NCons{Tree.Stmt{_kd, _ks, _b}, _r}:
      {==}
    case Tree.NCons{Tree.NNil{}, _r}:
      {==}
    case Tree.NCons{Tree.NCons{_a, _b}, _r}:
      {==}
    case Tree.NNil{}:
      {==}
    case Tree.Leaf{_tok}:
      {==}
    case Tree.Group{_o, _g, _cl}:
      {==}
    case Tree.Stmt{_kd, _ks, _b}:
      {==}

# Unit for True, Empty for False
def absurd_ty(bb: Bool) -> Type:
  match bb:
    case True{}:
      Unit
    case False{}:
      Empty

# True is not False
law true_false:
  for e: {True{} == False{} : Bool}
  Empty

def true_false(e):
  %e : absurd_ty(_)
  Unit{}

def Laws.percent_steps_over_name_and_at(rest, e):
  %Equal.sym(Bool, Bind.plan.rewrites(rest), True{}, e) :
    {Bool.pick(Bind.Mode, Bool.and(True{}, _), Bind.MSkip{Bind.MSkip{Bind.MTerm{}}}, Bind.MTerm{})
      == Bind.MSkip{Bind.MSkip{Bind.MTerm{}}} : Bind.Mode}
  {==}

def Laws.percent_alone_stays(rest, e):
  %Equal.sym(Bool, Bind.plan.rewrites(rest), False{}, e) :
    {Bool.pick(Bind.Mode, Bool.and(True{}, _), Bind.MSkip{Bind.MSkip{Bind.MTerm{}}}, Bind.MTerm{})
      == Bind.MTerm{} : Bind.Mode}
  {==}

def Laws.other_operator_stays(tt, rest, e):
  %Equal.sym(Bool, String.eq(tt, "%"), False{}, e) :
    {Bool.pick(Bind.Mode, Bool.and(_, Bind.plan.rewrites(rest)), Bind.MSkip{Bind.MSkip{Bind.MTerm{}}},
      Bind.MTerm{}) == Bind.MTerm{} : Bind.Mode}
  {==}

def Laws.other_kind_as_before(kk, tt, rest, e):
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
      Empty.absurd({Bind.plan.after(Bind.MTerm{}, Lex.TOp{}, tt, rest)
        == Bind.plan.lmode(Bind.MTerm{}, Lex.TOp{}, rest) : Bind.Mode}, true_false(e))
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

def Laws.other_mode_as_before(mode, kk, tt, rest, e):
  match mode:
    case Bind.MBlock{}:
      {==}
    case Bind.MCtors{}:
      {==}
    case Bind.MCtor{}:
      {==}
    case Bind.MHead{}:
      {==}
    case Bind.MName{}:
      {==}
    case Bind.MSig{}:
      {==}
    case Bind.MTele{_kind}:
      {==}
    case Bind.MTeleType{_kind}:
      {==}
    case Bind.MLhs{_outer, _kind}:
      {==}
    case Bind.MLhsType{_outer}:
      {==}
    case Bind.MTerm{}:
      Empty.absurd({Bind.plan.after(Bind.MTerm{}, kk, tt, rest)
        == Bind.plan.lmode(Bind.MTerm{}, kk, rest) : Bind.Mode}, true_false(e))
    case Bind.MSkip{_next}:
      {==}
    case Bind.MStop{}:
      {==}

def Laws.step_over_ends(_next, kk, _tt, _rest):
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
