# proofs of laws/TreeReadsStatements.bend
import Base
import ../src/syntax/lex.bend as Lex
import ../src/syntax/tree.bend as Tree
import ../laws/TreeReadsStatements.bend as Laws
import ../laws/defs/Chains.bend as D2
import ./lemmas/BoolEmptiness.bend as M1

def Laws.angle_opens_when_glued(kk, _tt, _glued):
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

def Laws.binds_in_own_tokens(h, _rest):
  match h:
    case Tree.Leaf{Lex.Tok{k, _t, _l, _c}}:
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
    case Tree.NNil{}:
      {==}
    case Tree.NCons{_a, _b}:
      {==}
    case Tree.Group{_o, _g, _cl}:
      {==}
    case Tree.Stmt{_kd, _ks, _b}:
      {==}

def Laws.binds_in_needs_tokens(kids, e):
  match kids:
    case Tree.NCons{h, r}:
      Empty.absurd({Tree.binds_in(Tree.NCons{h, r}) == False{} : Bool}, M1.true_false(e))
    case Tree.NNil{}:
      {==}
    case Tree.Leaf{_tok}:
      {==}
    case Tree.Group{_o, _g, _cl}:
      {==}
    case Tree.Stmt{_kd, _ks, _b}:
      {==}

def Laws.statement_kind_by_keyword(_tt):
  {==}

def Laws.arrow_names_a_binder(rest):
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
        case Lex.TUpper{}:
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
