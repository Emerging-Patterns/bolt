# proofs of laws/ArmsReportCoveredNatArms.bend
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/rules/tokens.bend as T
import ../src/lazy/lazy.bend as Lazy
import ../src/syntax/tree.bend as Tree
import ../src/rules/correctness/pick.bend as Pick
import ../src/rules/correctness/arms.bend as Arms
import ../laws/ArmsReportCoveredNatArms.bend as Laws
import ./lemmas/Nat.bend as M1
import ./lemmas/Pick.bend as M2

# the k an arm matches every Nat from, if any
def arms.up(aa: Arms.Arm) -> Maybe<&2, U32>:
  match aa:
    case Arms.APlus{k, t, l, c, n}:
      Some{k}
    case other:
      None{}

# the least Nat an arm matches, if any
def arms.lo(aa: Arms.Arm) -> Maybe<&2, U32>:
  match aa:
    case Arms.APlus{k, t, l, c, n}:
      Some{k}
    case Arms.ALit{k, l, c, n}:
      Some{k}
    case Arms.AOther{}:
      None{}

# the k of the widest arm so far, if any
def arms.floor(ww: Maybe<&2, Arms.Wide>) -> Maybe<&2, U32>:
  match ww:
    case None{}:
      None{}
    case Some{Arms.Wide{k, text}}:
      Some{k}

# a lone binder, inside `Succ{..}` or after `kn+`, to the rule and to the law
law arms.binder:
  for kk: Lex.TokKind
  {Arms.binder(kk) == Laws.arms.binder(kk) : Bool}

def arms.binder(kk):
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

# a picked from-k-up arm, read from above
law arms.pick_up:
  for b: Bool
  for +k: U32
  for t: String
  for l: U32
  for c: U32
  for n: U32
  {arms.up(Bool.pick(Arms.Arm, b, Arms.APlus{k, t, l, c, n}, Arms.AOther{})) == Bool.pick(Maybe<&2, U32>, b, Some{k},
      None{}) : Maybe<&2, U32>}

def arms.pick_up(b, _k, _t, _l, _c, _n):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# a from-k-up arm after `kn+`, its binder read by the rule's test and the law's
law arms.plus_up:
  for x: Bool
  for +b: Lex.TokKind
  for +k: U32
  for +t: String
  for +l: U32
  for +c: U32
  for +n: U32
  {arms.up(Bool.pick(Arms.Arm, Bool.and(x, Arms.binder(b)), Arms.APlus{k, t, l, c, n}, Arms.AOther{}))
    == Bool.pick(Maybe<&2, U32>, Bool.and(x, Laws.arms.binder(b)), Some{k}, None{}) : Maybe<&2, U32>}

def arms.plus_up(x, b, k, t, l, c, n):
  %Equal.sym(Bool, Arms.binder(b), Laws.arms.binder(b), arms.binder(b)) :
    {arms.up(Bool.pick(Arms.Arm, Bool.and(x, _), Arms.APlus{k, t, l, c, n}, Arms.AOther{}))
    == Bool.pick(Maybe<&2, U32>, Bool.and(x, Laws.arms.binder(b)), Some{k}, None{}) : Maybe<&2, U32>}
  arms.pick_up(Bool.and(x, Laws.arms.binder(b)), k, t, l, c, n)

# a picked from-k-up arm, read from below, when `or`ed with no `:`
law arms.pick_lo:
  for b: Bool
  for +k: U32
  for t: String
  for l: U32
  for c: U32
  for n: U32
  {arms.lo(Bool.pick(Arms.Arm, b, Arms.APlus{k, t, l, c, n}, Arms.AOther{})) == Bool.pick(Maybe<&2, U32>, Bool.or(b,
      False{}), Some{k}, None{}) : Maybe<&2, U32>}

def arms.pick_lo(b, _k, _t, _l, _c, _n):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the same, read from below
law arms.plus_lo:
  for x: Bool
  for +b: Lex.TokKind
  for +k: U32
  for +t: String
  for +l: U32
  for +c: U32
  for +n: U32
  {arms.lo(Bool.pick(Arms.Arm, Bool.and(x, Arms.binder(b)), Arms.APlus{k, t, l, c, n}, Arms.AOther{}))
    == Bool.pick(Maybe<&2, U32>, Bool.or(Bool.and(x, Laws.arms.binder(b)), False{}), Some{k}, None{})
    : Maybe<&2, U32>}

def arms.plus_lo(x, b, k, t, l, c, n):
  %Equal.sym(Bool, Arms.binder(b), Laws.arms.binder(b), arms.binder(b)) :
    {arms.lo(Bool.pick(Arms.Arm, Bool.and(x, _), Arms.APlus{k, t, l, c, n}, Arms.AOther{}))
    == Bool.pick(Maybe<&2, U32>, Bool.or(Bool.and(x, Laws.arms.binder(b)), False{}), Some{k}, None{})
    : Maybe<&2, U32>}
  arms.pick_lo(Bool.and(x, Laws.arms.binder(b)), k, t, l, c, n)

# a picked from-k-up arm, read from below
law arms.pick_lo1:
  for b: Bool
  for +k: U32
  for t: String
  for l: U32
  for c: U32
  for n: U32
  {arms.lo(Bool.pick(Arms.Arm, b, Arms.APlus{k, t, l, c, n}, Arms.AOther{})) == Bool.pick(Maybe<&2, U32>, b, Some{k},
      None{}) : Maybe<&2, U32>}

def arms.pick_lo1(b, _k, _t, _l, _c, _n):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# what follows a Nat literal, read by the rule and by the law, from above
law arms.shape_up:
  for rest: Tree.Node
  for +k: U32
  for +tt: String
  for +line: U32
  for +col: U32
  {arms.up(Arms.lit.shape(rest, k, tt, line, col)) == Bool.pick(Maybe<&2, U32>, Laws.arms.plus(rest), Some{k},
      None{}) : Maybe<&2, U32>}

def arms.shape_up(rest, k, tt, line, col):
  match rest:
    case Tree.Leaf{Lex.Tok{+k1, +x2, +l3, +c4}}:
      {==}
    case Tree.Group{+op5, +ks6, +cl7}:
      {==}
    case Tree.Stmt{+sk8, +sks9, +sb10}:
      {==}
    case Tree.NNil{}:
      {==}
    case Tree.NCons{+h11, +t12}:
      match h11:
        case Tree.Leaf{Lex.Tok{+k13, +x14, +l15, +c16}}:
          match k13:
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
              match t12:
                case Tree.Leaf{Lex.Tok{+k17, +x18, +l19, +c20}}:
                  {==}
                case Tree.Group{+op21, +ks22, +cl23}:
                  {==}
                case Tree.Stmt{+sk24, +sks25, +sb26}:
                  {==}
                case Tree.NNil{}:
                  {==}
                case Tree.NCons{+h27, +t28}:
                  match h27:
                    case Tree.Leaf{Lex.Tok{+k29, +x30, +l31, +c32}}:
                      match t28:
                        case Tree.Leaf{Lex.Tok{+k33, +x34, +l35, +c36}}:
                          {==}
                        case Tree.Group{+op37, +ks38, +cl39}:
                          {==}
                        case Tree.Stmt{+sk40, +sks41, +sb42}:
                          {==}
                        case Tree.NNil{}:
                          {==}
                        case Tree.NCons{+h43, +t44}:
                          match h43:
                            case Tree.Leaf{Lex.Tok{+k45, +x46, +l47, +c48}}:
                              match k45:
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
                                  arms.plus_up(String.eq(x14, "+"), k29, k, tt ++ "+" ++ x30, line, col, T.width(tt))
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
                            case Tree.Group{+op49, +ks50, +cl51}:
                              {==}
                            case Tree.Stmt{+sk52, +sks53, +sb54}:
                              {==}
                            case Tree.NNil{}:
                              {==}
                            case Tree.NCons{+h55, +t56}:
                              {==}
                    case Tree.Group{+op57, +ks58, +cl59}:
                      {==}
                    case Tree.Stmt{+sk60, +sks61, +sb62}:
                      {==}
                    case Tree.NNil{}:
                      {==}
                    case Tree.NCons{+h63, +t64}:
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
        case Tree.Group{+op65, +ks66, +cl67}:
          {==}
        case Tree.Stmt{+sk68, +sks69, +sb70}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{+h71, +t72}:
          {==}

# what follows a Nat literal, read by the rule and by the law, from below
law arms.shape_lo:
  for rest: Tree.Node
  for +k: U32
  for +tt: String
  for +line: U32
  for +col: U32
  {arms.lo(Arms.lit.shape(rest, k, tt, line, col)) == Bool.pick(Maybe<&2, U32>, Bool.or(Laws.arms.plus(rest),
      Laws.arms.exact(rest)), Some{k}, None{}) : Maybe<&2, U32>}

def arms.shape_lo(rest, k, tt, line, col):
  match rest:
    case Tree.Leaf{Lex.Tok{+k73, +x74, +l75, +c76}}:
      {==}
    case Tree.Group{+op77, +ks78, +cl79}:
      {==}
    case Tree.Stmt{+sk80, +sks81, +sb82}:
      {==}
    case Tree.NNil{}:
      {==}
    case Tree.NCons{+h83, +t84}:
      match h83:
        case Tree.Leaf{Lex.Tok{+k85, +x86, +l87, +c88}}:
          match k85:
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
              match t84:
                case Tree.Leaf{Lex.Tok{+k89, +x90, +l91, +c92}}:
                  {==}
                case Tree.Group{+op93, +ks94, +cl95}:
                  {==}
                case Tree.Stmt{+sk96, +sks97, +sb98}:
                  {==}
                case Tree.NNil{}:
                  {==}
                case Tree.NCons{+h99, +t100}:
                  match h99:
                    case Tree.Leaf{Lex.Tok{+k101, +x102, +l103, +c104}}:
                      match t100:
                        case Tree.Leaf{Lex.Tok{+k105, +x106, +l107, +c108}}:
                          {==}
                        case Tree.Group{+op109, +ks110, +cl111}:
                          {==}
                        case Tree.Stmt{+sk112, +sks113, +sb114}:
                          {==}
                        case Tree.NNil{}:
                          {==}
                        case Tree.NCons{+h115, +t116}:
                          match h115:
                            case Tree.Leaf{Lex.Tok{+k117, +x118, +l119, +c120}}:
                              match k117:
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
                                  arms.plus_lo(String.eq(x86, "+"), k101, k, tt ++ "+" ++ x102, line, col, T.width(tt))
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
                            case Tree.Group{+op121, +ks122, +cl123}:
                              {==}
                            case Tree.Stmt{+sk124, +sks125, +sb126}:
                              {==}
                            case Tree.NNil{}:
                              {==}
                            case Tree.NCons{+h127, +t128}:
                              {==}
                    case Tree.Group{+op129, +ks130, +cl131}:
                      {==}
                    case Tree.Stmt{+sk132, +sks133, +sb134}:
                      {==}
                    case Tree.NNil{}:
                      {==}
                    case Tree.NCons{+h135, +t136}:
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
        case Tree.Group{+op137, +ks138, +cl139}:
          {==}
        case Tree.Stmt{+sk140, +sks141, +sb142}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{+h143, +t144}:
          {==}

# a Nat literal's arm, once its value is read, from above
law arms.of_up:
  for mm: Maybe<&2, U32>
  for +tt: String
  for +rest: Tree.Node
  for +line: U32
  for +col: U32
  {arms.up(Arms.lit.of(mm, tt, rest, line, col)) == Laws.arms.num(mm, Laws.arms.plus(rest)) : Maybe<&2, U32>}

def arms.of_up(mm, tt, rest, line, col):
  match mm:
    case None{}:
      {==}
    case Some{k}:
      arms.shape_up(rest, k, tt, line, col)

# a Nat literal's arm, once its value is read, from below
law arms.of_lo:
  for mm: Maybe<&2, U32>
  for +tt: String
  for +rest: Tree.Node
  for +line: U32
  for +col: U32
  {arms.lo(Arms.lit.of(mm, tt, rest, line, col)) == Laws.arms.num(mm, Bool.or(Laws.arms.plus(rest),
      Laws.arms.exact(rest))) : Maybe<&2, U32>}

def arms.of_lo(mm, tt, rest, line, col):
  match mm:
    case None{}:
      {==}
    case Some{k}:
      arms.shape_lo(rest, k, tt, line, col)

# a case pattern's arm, to the rule and to the law, from above
law arms.up_is:
  for pat: Tree.Node
  {arms.up(Arms.arm(pat)) == Laws.arms.from(pat) : Maybe<&2, U32>}

def arms.up_is(pat):
  match pat:
    case Tree.Leaf{Lex.Tok{+k145, +x146, +l147, +c148}}:
      {==}
    case Tree.Group{+op149, +ks150, +cl151}:
      {==}
    case Tree.Stmt{+sk152, +sks153, +sb154}:
      {==}
    case Tree.NNil{}:
      {==}
    case Tree.NCons{+h155, +t156}:
      match h155:
        case Tree.Leaf{Lex.Tok{+k157, +x158, +l159, +c160}}:
          match k157:
            case Lex.TName{}:
              {==}
            case Lex.TUpper{}:
              match t156:
                case Tree.Leaf{Lex.Tok{+k161, +x162, +l163, +c164}}:
                  {==}
                case Tree.Group{+op165, +ks166, +cl167}:
                  {==}
                case Tree.Stmt{+sk168, +sks169, +sb170}:
                  {==}
                case Tree.NNil{}:
                  {==}
                case Tree.NCons{+h171, +t172}:
                  match h171:
                    case Tree.Leaf{Lex.Tok{+k173, +x174, +l175, +c176}}:
                      {==}
                    case Tree.Group{+op177, +ks178, +cl179}:
                      match ks178:
                        case Tree.Leaf{Lex.Tok{+k180, +x181, +l182, +c183}}:
                          {==}
                        case Tree.Group{+op184, +ks185, +cl186}:
                          {==}
                        case Tree.Stmt{+sk187, +sks188, +sb189}:
                          {==}
                        case Tree.NNil{}:
                          {==}
                        case Tree.NCons{+h190, +t191}:
                          match h190:
                            case Tree.Leaf{Lex.Tok{+k192, +x193, +l194, +c195}}:
                              match t191:
                                case Tree.Leaf{Lex.Tok{+k196, +x197, +l198, +c199}}:
                                  {==}
                                case Tree.Group{+op200, +ks201, +cl202}:
                                  {==}
                                case Tree.Stmt{+sk203, +sks204, +sb205}:
                                  {==}
                                case Tree.NNil{}:
                                  Equal.trans(Maybe<&2, U32>, arms.up(Bool.pick(Arms.Arm, Bool.and(String.eq(x158,
                                    "Succ"), Arms.binder(k192)), Arms.APlus{1, "Succ{" ++ x193 ++ "}", l159, c160, 4},
                                    Arms.AOther{})),
                                    arms.up(Bool.pick(Arms.Arm, Bool.and(String.eq(x158, "Succ"),
                                      Laws.arms.binder(k192)), Arms.APlus{1, "Succ{" ++ x193 ++ "}", l159, c160, 4},
                                      Arms.AOther{})),
                                    Bool.pick(Maybe<&2, U32>, Bool.and(String.eq(x158, "Succ"),
                                      Laws.arms.binder(k192)), Some{1}, None{}),
                                    Equal.cong(Bool, Maybe<&2, U32>, z => arms.up(Bool.pick(Arms.Arm,
                                      Bool.and(String.eq(x158, "Succ"), z), Arms.APlus{1, "Succ{" ++ x193 ++ "}", l159,
                                      c160, 4}, Arms.AOther{})),
                                      Arms.binder(k192), Laws.arms.binder(k192), arms.binder(k192)),
                                    arms.pick_up(Bool.and(String.eq(x158, "Succ"), Laws.arms.binder(k192)), 1,
                                      "Succ{" ++ x193 ++ "}", l159, c160, 4))
                                case Tree.NCons{+h206, +t207}:
                                  {==}
                            case Tree.Group{+op208, +ks209, +cl210}:
                              {==}
                            case Tree.Stmt{+sk211, +sks212, +sb213}:
                              {==}
                            case Tree.NNil{}:
                              {==}
                            case Tree.NCons{+h214, +t215}:
                              {==}
                    case Tree.Stmt{+sk216, +sks217, +sb218}:
                      {==}
                    case Tree.NNil{}:
                      {==}
                    case Tree.NCons{+h219, +t220}:
                      {==}
            case Lex.TDotted{}:
              {==}
            case Lex.TWild{}:
              {==}
            case Lex.TKey{}:
              {==}
            case Lex.TNum{}:
              arms.of_up(T.nat_value(x158), x158, t156, l159, c160)
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
        case Tree.Group{+op221, +ks222, +cl223}:
          {==}
        case Tree.Stmt{+sk224, +sks225, +sb226}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{+h227, +t228}:
          {==}

# a case pattern's arm, to the rule and to the law, from below
law arms.lo_is:
  for pat: Tree.Node
  {arms.lo(Arms.arm(pat)) == Laws.arms.least(pat) : Maybe<&2, U32>}

def arms.lo_is(pat):
  match pat:
    case Tree.Leaf{Lex.Tok{+k229, +x230, +l231, +c232}}:
      {==}
    case Tree.Group{+op233, +ks234, +cl235}:
      {==}
    case Tree.Stmt{+sk236, +sks237, +sb238}:
      {==}
    case Tree.NNil{}:
      {==}
    case Tree.NCons{+h239, +t240}:
      match h239:
        case Tree.Leaf{Lex.Tok{+k241, +x242, +l243, +c244}}:
          match k241:
            case Lex.TName{}:
              {==}
            case Lex.TUpper{}:
              match t240:
                case Tree.Leaf{Lex.Tok{+k245, +x246, +l247, +c248}}:
                  {==}
                case Tree.Group{+op249, +ks250, +cl251}:
                  {==}
                case Tree.Stmt{+sk252, +sks253, +sb254}:
                  {==}
                case Tree.NNil{}:
                  {==}
                case Tree.NCons{+h255, +t256}:
                  match h255:
                    case Tree.Leaf{Lex.Tok{+k257, +x258, +l259, +c260}}:
                      {==}
                    case Tree.Group{+op261, +ks262, +cl263}:
                      match ks262:
                        case Tree.Leaf{Lex.Tok{+k264, +x265, +l266, +c267}}:
                          {==}
                        case Tree.Group{+op268, +ks269, +cl270}:
                          {==}
                        case Tree.Stmt{+sk271, +sks272, +sb273}:
                          {==}
                        case Tree.NNil{}:
                          {==}
                        case Tree.NCons{+h274, +t275}:
                          match h274:
                            case Tree.Leaf{Lex.Tok{+k276, +x277, +l278, +c279}}:
                              match t275:
                                case Tree.Leaf{Lex.Tok{+k280, +x281, +l282, +c283}}:
                                  {==}
                                case Tree.Group{+op284, +ks285, +cl286}:
                                  {==}
                                case Tree.Stmt{+sk287, +sks288, +sb289}:
                                  {==}
                                case Tree.NNil{}:
                                  Equal.trans(Maybe<&2, U32>, arms.lo(Bool.pick(Arms.Arm, Bool.and(String.eq(x242,
                                    "Succ"), Arms.binder(k276)), Arms.APlus{1, "Succ{" ++ x277 ++ "}", l243, c244, 4},
                                    Arms.AOther{})),
                                    arms.lo(Bool.pick(Arms.Arm, Bool.and(String.eq(x242, "Succ"),
                                      Laws.arms.binder(k276)), Arms.APlus{1, "Succ{" ++ x277 ++ "}", l243, c244, 4},
                                      Arms.AOther{})),
                                    Bool.pick(Maybe<&2, U32>, Bool.and(String.eq(x242, "Succ"),
                                      Laws.arms.binder(k276)), Some{1}, None{}),
                                    Equal.cong(Bool, Maybe<&2, U32>, z => arms.lo(Bool.pick(Arms.Arm,
                                      Bool.and(String.eq(x242, "Succ"), z), Arms.APlus{1, "Succ{" ++ x277 ++ "}", l243,
                                      c244, 4}, Arms.AOther{})),
                                      Arms.binder(k276), Laws.arms.binder(k276), arms.binder(k276)),
                                    arms.pick_lo1(Bool.and(String.eq(x242, "Succ"), Laws.arms.binder(k276)), 1,
                                      "Succ{" ++ x277 ++ "}", l243, c244, 4))
                                case Tree.NCons{+h290, +t291}:
                                  {==}
                            case Tree.Group{+op292, +ks293, +cl294}:
                              {==}
                            case Tree.Stmt{+sk295, +sks296, +sb297}:
                              {==}
                            case Tree.NNil{}:
                              {==}
                            case Tree.NCons{+h298, +t299}:
                              {==}
                    case Tree.Stmt{+sk300, +sks301, +sb302}:
                      {==}
                    case Tree.NNil{}:
                      {==}
                    case Tree.NCons{+h303, +t304}:
                      {==}
            case Lex.TDotted{}:
              {==}
            case Lex.TWild{}:
              {==}
            case Lex.TKey{}:
              {==}
            case Lex.TNum{}:
              arms.of_lo(T.nat_value(x242), x242, t240, l243, c244)
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
        case Tree.Group{+op305, +ks306, +cl307}:
          {==}
        case Tree.Stmt{+sk308, +sks309, +sb310}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{+h311, +t312}:
          {==}

# one scrutinee, to the rule and to the law
law arms.single:
  for kids: Tree.Node
  {Arms.single(kids) == Laws.arms.single(kids) : Bool}

def arms.single(kids):
  match kids:
    case Tree.Leaf{Lex.Tok{+k313, +x314, +l315, +c316}}:
      {==}
    case Tree.Group{+op317, +ks318, +cl319}:
      {==}
    case Tree.Stmt{+sk320, +sks321, +sb322}:
      {==}
    case Tree.NNil{}:
      {==}
    case Tree.NCons{+h323, +t324}:
      match h323:
        case Tree.Leaf{Lex.Tok{+k325, +x326, +l327, +c328}}:
          match k325:
            case Lex.TName{}:
              {==}
            case Lex.TUpper{}:
              {==}
            case Lex.TDotted{}:
              {==}
            case Lex.TWild{}:
              {==}
            case Lex.TKey{}:
              match t324:
                case Tree.Leaf{Lex.Tok{+k329, +x330, +l331, +c332}}:
                  {==}
                case Tree.Group{+op333, +ks334, +cl335}:
                  {==}
                case Tree.Stmt{+sk336, +sks337, +sb338}:
                  {==}
                case Tree.NNil{}:
                  {==}
                case Tree.NCons{+h339, +t340}:
                  match t340:
                    case Tree.Leaf{Lex.Tok{+k341, +x342, +l343, +c344}}:
                      {==}
                    case Tree.Group{+op345, +ks346, +cl347}:
                      {==}
                    case Tree.Stmt{+sk348, +sks349, +sb350}:
                      {==}
                    case Tree.NNil{}:
                      {==}
                    case Tree.NCons{+h351, +t352}:
                      match h351:
                        case Tree.Leaf{Lex.Tok{+k353, +x354, +l355, +c356}}:
                          match k353:
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
                              match t352:
                                case Tree.Leaf{Lex.Tok{+k357, +x358, +l359, +c360}}:
                                  {==}
                                case Tree.Group{+op361, +ks362, +cl363}:
                                  {==}
                                case Tree.Stmt{+sk364, +sks365, +sb366}:
                                  {==}
                                case Tree.NNil{}:
                                  {==}
                                case Tree.NCons{+h367, +t368}:
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
                        case Tree.Group{+op369, +ks370, +cl371}:
                          {==}
                        case Tree.Stmt{+sk372, +sks373, +sb374}:
                          {==}
                        case Tree.NNil{}:
                          {==}
                        case Tree.NCons{+h375, +t376}:
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
        case Tree.Group{+op377, +ks378, +cl379}:
          {==}
        case Tree.Stmt{+sk380, +sks381, +sb382}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{+h383, +t384}:
          {==}

# an arm against the widest one above: a finding exactly when the law's hit
law arms.verdict:
  for ww: Maybe<&2, Arms.Wide>
  for aa: Arms.Arm
  for +path: String
  for -more: List<&2, F.Finding>
  for -m: Nat
  for ih: {List.length(&2, F.Finding, more) == m : Nat}
  {List.length(&2, F.Finding, Arms.verdict(ww, aa, path, more)) == Bool.pick(Nat, Laws.arms.hit(arms.floor(ww),
      arms.lo(aa)), 1n+m, m) : Nat}

def arms.verdict(ww, aa, path, more, m, ih):
  match ww:
    case None{}:
      ih
    case Some{Arms.Wide{+k, +text}}:
      match aa:
        case Arms.APlus{+j, t, +l, +c, +n}:
          M1.nat.pick(U32.is_ge(j, k), F.Finding{path, l, c, n, "arms",
            "Unreachable: the case " ++ text ++ " above already matches everything from " ++ U32.show(j)
              ++ "n up; put narrower arms first."}, more, m, ih)
        case Arms.ALit{+j, +l, +c, +n}:
          M1.nat.pick(U32.is_ge(j, k), F.Finding{path, l, c, n, "arms",
            "Unreachable: the case " ++ text ++ " above already matches " ++ U32.show(j)
              ++ "n; put narrower arms first."}, more, m, ih)
        case Arms.AOther{}:
          ih

# a picked widest arm, read by its k
law arms.pick_floor:
  for b: Bool
  for +j: U32
  for t2: String
  for +k: U32
  for text: String
  {arms.floor(Bool.pick(Maybe<&2, Arms.Wide>, b, Some{Arms.Wide{j, t2}}, Some{Arms.Wide{k, text}}))
    == Bool.pick(Maybe<&2, U32>, b, Some{j}, Some{k}) : Maybe<&2, U32>}

def arms.pick_floor(b, _j, _t2, _k, _text):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the widest arm after one more, read by its k, is the law's lower bound
law arms.widen:
  for ww: Maybe<&2, Arms.Wide>
  for aa: Arms.Arm
  {arms.floor(Arms.widen(ww, aa)) == Laws.arms.lower(arms.floor(ww), arms.up(aa)) : Maybe<&2, U32>}

def arms.widen(ww, aa):
  match ww:
    case None{}:
      match aa:
        case Arms.APlus{j, t2, l, c, n}:
          {==}
        case Arms.ALit{j, l, c, n}:
          {==}
        case Arms.AOther{}:
          {==}
    case Some{Arms.Wide{+k, +text}}:
      match aa:
        case Arms.APlus{+j, +t2, l, c, n}:
          arms.pick_floor(U32.is_lt(j, k), j, t2, k, text)
        case Arms.ALit{j, l, c, n}:
          {==}
        case Arms.AOther{}:
          {==}

# one case arm onto the rest of a match the law holds for
law arms.case:
  for +pat: Tree.Node
  for +rest: Tree.Node
  for +wide: Maybe<&2, Arms.Wide>
  for +path: String
  for ih: {List.length(&2, F.Finding, Arms.arms(rest, Arms.widen(wide, Arms.arm(pat)),
    path)) == Laws.arms.covered(rest, arms.floor(Arms.widen(wide, Arms.arm(pat)))) : Nat}
  {List.length(&2, F.Finding, Arms.verdict(wide, Arms.arm(pat), path, Arms.arms(rest, Arms.widen(wide, Arms.arm(pat)),
      path))) == Bool.pick(Nat, Laws.arms.hit(arms.floor(wide), Laws.arms.least(pat)), 1n+Laws.arms.covered(rest,
      Laws.arms.lower(arms.floor(wide), Laws.arms.from(pat))), Laws.arms.covered(rest,
      Laws.arms.lower(arms.floor(wide), Laws.arms.from(pat)))) : Nat}

def arms.case(pat, rest, wide, path, ih):
  Equal.trans(Nat, List.length(&2, F.Finding, Arms.verdict(wide, Arms.arm(pat), path, Arms.arms(rest, Arms.widen(wide,
    Arms.arm(pat)), path))),
    Bool.pick(Nat, Laws.arms.hit(arms.floor(wide), arms.lo(Arms.arm(pat))), 1n+Laws.arms.covered(rest,
      arms.floor(Arms.widen(wide, Arms.arm(pat)))), Laws.arms.covered(rest, arms.floor(Arms.widen(wide,
      Arms.arm(pat))))),
    Bool.pick(Nat, Laws.arms.hit(arms.floor(wide), Laws.arms.least(pat)), 1n+Laws.arms.covered(rest,
      Laws.arms.lower(arms.floor(wide), Laws.arms.from(pat))), Laws.arms.covered(rest,
      Laws.arms.lower(arms.floor(wide), Laws.arms.from(pat)))),
    arms.verdict(wide, Arms.arm(pat), path, Arms.arms(rest, Arms.widen(wide, Arms.arm(pat)), path),
      Laws.arms.covered(rest, arms.floor(Arms.widen(wide, Arms.arm(pat)))), ih),
    Equal.trans(Nat, Bool.pick(Nat, Laws.arms.hit(arms.floor(wide), arms.lo(Arms.arm(pat))), 1n+Laws.arms.covered(rest,
      arms.floor(Arms.widen(wide, Arms.arm(pat)))), Laws.arms.covered(rest, arms.floor(Arms.widen(wide,
      Arms.arm(pat))))),
      Bool.pick(Nat, Laws.arms.hit(arms.floor(wide), Laws.arms.least(pat)), 1n+Laws.arms.covered(rest,
        arms.floor(Arms.widen(wide, Arms.arm(pat)))), Laws.arms.covered(rest, arms.floor(Arms.widen(wide,
        Arms.arm(pat))))),
      Bool.pick(Nat, Laws.arms.hit(arms.floor(wide), Laws.arms.least(pat)), 1n+Laws.arms.covered(rest,
        Laws.arms.lower(arms.floor(wide), Laws.arms.from(pat))), Laws.arms.covered(rest,
        Laws.arms.lower(arms.floor(wide), Laws.arms.from(pat)))),
      Equal.cong(Maybe<&2, U32>, Nat, z => Bool.pick(Nat, Laws.arms.hit(arms.floor(wide), z),
        1n+Laws.arms.covered(rest, arms.floor(Arms.widen(wide, Arms.arm(pat)))), Laws.arms.covered(rest,
        arms.floor(Arms.widen(wide, Arms.arm(pat))))),
        arms.lo(Arms.arm(pat)), Laws.arms.least(pat), arms.lo_is(pat)),
      Equal.cong(Maybe<&2, U32>, Nat,
        z => Bool.pick(Nat, Laws.arms.hit(arms.floor(wide), Laws.arms.least(pat)), 1n+Laws.arms.covered(rest, z),
          Laws.arms.covered(rest, z)),
        arms.floor(Arms.widen(wide, Arms.arm(pat))), Laws.arms.lower(arms.floor(wide), Laws.arms.from(pat)),
        Equal.trans(Maybe<&2, U32>, arms.floor(Arms.widen(wide, Arms.arm(pat))), Laws.arms.lower(arms.floor(wide),
          arms.up(Arms.arm(pat))),
          Laws.arms.lower(arms.floor(wide), Laws.arms.from(pat)),
          arms.widen(wide, Arms.arm(pat)),
          Equal.cong(Maybe<&2, U32>, Maybe<&2, U32>, z => Laws.arms.lower(arms.floor(wide), z), arms.up(Arms.arm(pat)),
            Laws.arms.from(pat),
            arms.up_is(pat))))))

# a match's arms, the widest above them read by its k
law arms.go:
  for body: Tree.Node
  for +wide: Maybe<&2, Arms.Wide>
  for +path: String
  {List.length(&2, F.Finding, Arms.arms(body, wide, path)) == Laws.arms.covered(body, arms.floor(wide)) : Nat}

def arms.go(body, wide, path):
  match body:
    case Tree.Leaf{Lex.Tok{+k385, +x386, +l387, +c388}}:
      {==}
    case Tree.Group{+op389, +ks390, +cl391}:
      {==}
    case Tree.Stmt{+sk392, +sks393, +sb394}:
      {==}
    case Tree.NNil{}:
      {==}
    case Tree.NCons{+h395, +t396}:
      match h395:
        case Tree.Leaf{Lex.Tok{+k397, +x398, +l399, +c400}}:
          arms.go(t396, wide, path)
        case Tree.Group{+op401, +ks402, +cl403}:
          arms.go(t396, wide, path)
        case Tree.Stmt{+sk404, +sks405, +sb406}:
          match sk404:
            case Tree.SDef{}:
              arms.go(t396, wide, path)
            case Tree.SType{}:
              arms.go(t396, wide, path)
            case Tree.SLaw{}:
              arms.go(t396, wide, path)
            case Tree.SImport{}:
              arms.go(t396, wide, path)
            case Tree.SCase{}:
              arms.case(T.pattern(sks405), t396, wide, path,
                arms.go(t396, Arms.widen(wide, Arms.arm(T.pattern(sks405))), path))
            case Tree.SFor{}:
              arms.go(t396, wide, path)
            case Tree.SLet{}:
              arms.go(t396, wide, path)
            case Tree.STerm{}:
              arms.go(t396, wide, path)
        case Tree.NNil{}:
          arms.go(t396, wide, path)
        case Tree.NCons{+h407, +t408}:
          arms.go(t396, wide, path)

# one statement onto the rest, its body and the rest both holding the law
law arms.stmt:
  for +kids: Tree.Node
  for +body: Tree.Node
  for +rest: Tree.Node
  for +path: String
  for ihb: {List.length(&2, F.Finding, Arms.walk(body, path)) == Laws.arms_count(body) : Nat}
  for ihr: {List.length(&2, F.Finding, Arms.walk(rest, path)) == Laws.arms_count(rest) : Nat}
  {List.length(&2, F.Finding, List.concat(&2, F.Finding, [Lazy.stop(List<&2, F.Finding>, Bool.not(Arms.single(kids)),
      [], _u => Arms.arms(body, None{}, path)), Arms.walk(body, path), Arms.walk(rest, path)]))
    == Nat.add(Bool.pick(Nat, Laws.arms.single(kids), Laws.arms.covered(body, None{}), 0n),
      Nat.add(Laws.arms_count(body), Laws.arms_count(rest))) : Nat}

def arms.stmt(kids, body, rest, path, ihb, ihr):
  Equal.trans(Nat, List.length(&2, F.Finding, List.concat(&2, F.Finding, [Lazy.stop(List<&2, F.Finding>,
    Bool.not(Arms.single(kids)), [], _u => Arms.arms(body, None{}, path)), Arms.walk(body, path), Arms.walk(rest,
    path)])),
    Nat.add(List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, Bool.not(Arms.single(kids)), [],
      _u => Arms.arms(body, None{}, path))), Nat.add(List.length(&2, F.Finding, Arms.walk(body, path)), List.length(&2,
      F.Finding, Arms.walk(rest, path)))),
    Nat.add(Bool.pick(Nat, Laws.arms.single(kids), Laws.arms.covered(body, None{}), 0n), Nat.add(Laws.arms_count(body),
      Laws.arms_count(rest))),
    M2.arms.cat(Lazy.stop(List<&2, F.Finding>, Bool.not(Arms.single(kids)), [], _u => Arms.arms(body, None{}, path)),
      Arms.walk(body, path), Arms.walk(rest, path)),
    M2.arms.add3(List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, Bool.not(Arms.single(kids)), [],
      _u => Arms.arms(body, None{}, path))), Bool.pick(Nat, Laws.arms.single(kids), Laws.arms.covered(body, None{}),
      0n), List.length(&2, F.Finding, Arms.walk(body, path)), Laws.arms_count(body), List.length(&2, F.Finding,
      Arms.walk(rest, path)), Laws.arms_count(rest),
      Equal.trans(Nat, List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, Bool.not(Arms.single(kids)), [],
        _u => Arms.arms(body, None{}, path))), Bool.pick(Nat, Bool.not(Arms.single(kids)), 0n, Laws.arms.covered(body,
        None{})), Bool.pick(Nat, Laws.arms.single(kids), Laws.arms.covered(body, None{}), 0n),
        M2.param.stop(Bool.not(Arms.single(kids)), Arms.arms(body, None{}, path), Laws.arms.covered(body, None{}),
          arms.go(body, None{}, path)),
        Equal.trans(Nat, Bool.pick(Nat, Bool.not(Arms.single(kids)), 0n, Laws.arms.covered(body, None{})),
          Bool.pick(Nat, Arms.single(kids), Laws.arms.covered(body, None{}), 0n), Bool.pick(Nat,
            Laws.arms.single(kids), Laws.arms.covered(body, None{}), 0n),
          M2.arms.flip(Arms.single(kids), Laws.arms.covered(body, None{})),
          Equal.cong(Bool, Nat, z => Bool.pick(Nat, z, Laws.arms.covered(body, None{}), 0n), Arms.single(kids),
            Laws.arms.single(kids),
            arms.single(kids)))),
      ihb, ihr))

# every statement at any depth, each single-scrutinee match's arms read
law arms.walk:
  for nn: Tree.Node
  for +path: String
  {List.length(&2, F.Finding, Arms.walk(nn, path)) == Laws.arms_count(nn) : Nat}

def arms.walk(nn, path):
  match nn:
    case Tree.Leaf{Lex.Tok{+k409, +x410, +l411, +c412}}:
      {==}
    case Tree.Group{+op413, +ks414, +cl415}:
      {==}
    case Tree.Stmt{+sk416, +sks417, +sb418}:
      {==}
    case Tree.NNil{}:
      {==}
    case Tree.NCons{+h419, +t420}:
      match h419:
        case Tree.Leaf{Lex.Tok{+k421, +x422, +l423, +c424}}:
          arms.walk(t420, path)
        case Tree.Group{+op425, +ks426, +cl427}:
          arms.walk(t420, path)
        case Tree.Stmt{+sk428, +sks429, +sb430}:
          arms.stmt(sks429, sb430, t420, path, arms.walk(sb430, path), arms.walk(t420, path))
        case Tree.NNil{}:
          arms.walk(t420, path)
        case Tree.NCons{+h431, +t432}:
          arms.walk(t420, path)

def Laws.arms_counts(path, _text, _toks, tree, _bound, _items):
  arms.walk(tree, path)
