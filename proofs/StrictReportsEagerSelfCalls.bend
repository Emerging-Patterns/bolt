# proofs of laws/StrictReportsEagerSelfCalls.bend
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/lazy/lazy.bend as Lazy
import ../src/syntax/tree.bend as Tree
import ../src/rules/calls.bend as Calls
import ../src/rules/correctness/pick.bend as Pick
import ../src/rules/pedantic/strict.bend as Strict
import ../laws/StrictReportsEagerSelfCalls.bend as Laws
import ./lemmas/Nat.bend as M1
import ./lemmas/Pick.bend as M2

# `&&` or `||` in a stretch, to the rule and to the law, past one token
law strict.segk:
  for k: Lex.TokKind
  for +t: String
  for l: U32
  for c: U32
  for +rest: Tree.Node
  for ih: {Strict.seg_op(rest) == Laws.strict.ops(rest) : Bool}
  {Strict.seg_op(Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}}, rest})
    == Laws.strict.ops(Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}}, rest}) : Bool}

def strict.segk(k, t, _l, _c, rest, ih):
  match k:
    case Lex.TName{}:
      ih
    case Lex.TUpper{}:
      ih
    case Lex.TDotted{}:
      ih
    case Lex.TWild{}:
      ih
    case Lex.TKey{}:
      ih
    case Lex.TNum{}:
      ih
    case Lex.TStr{}:
      ih
    case Lex.TChar{}:
      ih
    case Lex.TComment{}:
      ih
    case Lex.TSpace{}:
      ih
    case Lex.TNewline{}:
      ih
    case Lex.TOp{}:
      Equal.cong(Bool, Bool, x => Bool.or(Strict.logic(t), x), Strict.seg_op(rest), Laws.strict.ops(rest), ih)
    case Lex.TColon{}:
      ih
    case Lex.TEq{}:
      ih
    case Lex.TBind{}:
      ih
    case Lex.TArrow{}:
      ih
    case Lex.TLam{}:
      {==}
    case Lex.TAll{}:
      ih
    case Lex.TAmp{}:
      ih
    case Lex.TOpen{}:
      ih
    case Lex.TClose{}:
      ih
    case Lex.TComma{}:
      {==}

# `&&` or `||` in a stretch, to the rule and to the law
law strict.seg:
  for nn: Tree.Node
  {Strict.seg_op(nn) == Laws.strict.ops(nn) : Bool}

def strict.seg(nn):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{k, +t, l, c}:
              strict.segk(k, t, l, c, rest, strict.seg(rest))
        case Tree.Group{open, kids, close}:
          strict.seg(rest)
        case Tree.Stmt{kind, kids, body}:
          strict.seg(rest)
        case Tree.NNil{}:
          strict.seg(rest)
        case Tree.NCons{x, y}:
          strict.seg(rest)
    case Tree.Leaf{tok}:
      {==}
    case Tree.Group{open, kids, close}:
      {==}
    case Tree.Stmt{kind, kids, body}:
      {==}
    case Tree.NNil{}:
      {==}

# the walk at a hot the law's count reaches another way
law strict.hot:
  for +nn: Tree.Node
  for +name: String
  for +path: String
  for +outer: Bool
  for +h1: Bool
  for +h2: Bool
  for e: {h1 == h2 : Bool}
  for ih: {List.length(&2, F.Finding, Strict.walk(nn, name, path, outer, h1))
    == Laws.strict.count(nn, name, outer, h1) : Nat}
  {List.length(&2, F.Finding, Strict.walk(nn, name, path, outer, h1)) == Laws.strict.count(nn, name, outer, h2) : Nat}

def strict.hot(nn, name, path, outer, h1, h2, e, ih):
  Equal.trans(Nat, List.length(&2, F.Finding, Strict.walk(nn, name, path, outer, h1)), Laws.strict.count(nn, name,
    outer, h1), Laws.strict.count(nn, name, outer, h2), ih,
    Equal.cong(Bool, Nat, hh => Laws.strict.count(nn, name, outer, hh), h1, h2, e))

# past a comma: the next stretch is hot in an operand or by its own `&&`/`||`
law strict.comma:
  for +rest: Tree.Node
  for +name: String
  for +path: String
  for +outer: Bool
  for ih: {List.length(&2, F.Finding, Strict.walk(rest, name, path, outer, Bool.or(outer, Strict.seg_op(rest))))
    == Laws.strict.count(rest, name, outer, Bool.or(outer, Strict.seg_op(rest))) : Nat}
  {List.length(&2, F.Finding, Strict.walk(rest, name, path, outer, Bool.or(outer, Strict.seg_op(rest))))
    == Laws.strict.count(rest, name, outer, Bool.or(outer, Laws.strict.ops(rest))) : Nat}

def strict.comma(rest, name, path, outer, ih):
  strict.hot(rest, name, path, outer, Bool.or(outer, Strict.seg_op(rest)), Bool.or(outer, Laws.strict.ops(rest)),
    Equal.cong(Bool, Bool, x => Bool.or(outer, x), Strict.seg_op(rest), Laws.strict.ops(rest), strict.seg(rest)), ih)

# past a `=>`: the lambda body is hot only by its own `&&`/`||`
law strict.lam:
  for +rest: Tree.Node
  for +name: String
  for +path: String
  for +outer: Bool
  for ih: {List.length(&2, F.Finding, Strict.walk(rest, name, path, outer, Strict.seg_op(rest)))
    == Laws.strict.count(rest, name, outer, Strict.seg_op(rest)) : Nat}
  {List.length(&2, F.Finding, Strict.walk(rest, name, path, outer, Strict.seg_op(rest)))
    == Laws.strict.count(rest, name, outer, Laws.strict.ops(rest)) : Nat}

def strict.lam(rest, name, path, outer, ih):
  strict.hot(rest, name, path, outer, Strict.seg_op(rest), Laws.strict.ops(rest), strict.seg(rest), ih)

# is the group after a name an operand: the stretch is hot, or it is the `(`
# of `Bool.and` or `Bool.or`
def strict.inner(+hot: Bool, +o: String, +t: String) -> Bool:
  Bool.or(hot, Bool.and(String.eq(o, "("), Bool.or(String.eq(t, "Bool.and"), String.eq(t, "Bool.or"))))

# a name, then a group: a finding when the name is the def, the group a
# `(` call and the stretch hot; the group an operand when the name is
# `Bool.and` or `Bool.or` or the stretch is hot
law strict.call:
  for +t: String
  for +l: U32
  for +c: U32
  for ok: Lex.TokKind
  for +o: String
  for ol: U32
  for oc: U32
  for +kids: Tree.Node
  for close: Maybe<&2, Lex.Tok>
  for +r2: Tree.Node
  for +name: String
  for +path: String
  for +outer: Bool
  for +hot: Bool
  for ik: {List.length(&2, F.Finding, Strict.walk(kids, name, path, strict.inner(hot, o, t), Bool.or(strict.inner(hot,
    o, t), Strict.seg_op(kids))))
      == Laws.strict.count(kids, name, strict.inner(hot, o, t), Bool.or(strict.inner(hot, o, t),
        Strict.seg_op(kids))) : Nat}
  for ir: {List.length(&2, F.Finding, Strict.walk(r2, name, path, outer, hot))
    == Laws.strict.count(r2, name, outer, hot) : Nat}
  {List.length(&2, F.Finding, Strict.walk(Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, t, l, c}},
    Tree.NCons{Tree.Group{Lex.Tok{ok, o, ol, oc}, kids, close}, r2}}, name, path, outer, hot))
      == Laws.strict.count(Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, t, l, c}}, Tree.NCons{Tree.Group{Lex.Tok{ok, o, ol,
        oc}, kids, close}, r2}}, name, outer, hot) : Nat}

def strict.call(t, l, c, _ok, o, _ol, _oc, kids, _close, r2, name, path, outer, hot, ik, ir):
  +call = String.eq(o, "(")
  +inner = strict.inner(hot, o, t)
  +hk = Bool.or(inner, Strict.seg_op(kids))
  +fk = Strict.walk(kids, name, path, inner, hk)
  +fr = Strict.walk(r2, name, path, outer, hot)
  +ck = Laws.strict.count(kids, name, inner, Bool.or(inner, Laws.strict.ops(kids)))
  +cr = Laws.strict.count(r2, name, outer, hot)
  M1.nat.pick(Bool.and(Bool.and(call, String.eq(t, name)), hot),
    F.Finding{path, l, c, U32.from_nat(String.length(name)), "strict",
      name ++ " calls itself inside Bool.and or Bool.or, which evaluate both sides, so there is no short-circuit; match on the Bool in a helper."},
    List.concat(&2, F.Finding, [fk, fr]), Nat.add(ck, cr),
    M2.pick.join(fk, List.append(&2, F.Finding, fr, Nil{}), ck, cr,
      strict.hot(kids, name, path, inner, hk, Bool.or(inner, Laws.strict.ops(kids)),
        Equal.cong(Bool, Bool, x => Bool.or(inner, x), Strict.seg_op(kids), Laws.strict.ops(kids),
          strict.seg(kids)), ik),
      M2.pick.last(fr, cr, ir)))

def Laws.strict_walk_counts(nn, name, path, outer, hot):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{k, +t, +l, +c}:
              match k:
                case Lex.TName{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              strict.call(t, l, c, ok, o, ol, oc, kids, close, r2, name, path, outer, hot,
                                  Laws.strict_walk_counts(kids, name, path, strict.inner(hot, o, t),
                                    Bool.or(strict.inner(hot, o, t), Strict.seg_op(kids))),
                                  Laws.strict_walk_counts(r2, name, path, outer, hot))
                        case Tree.Leaf{x}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.Stmt{kind, kids, body}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NNil{}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NCons{x, y}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Leaf{x}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Group{open, kids, close}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Stmt{kind, kids, body}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.NNil{}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                case Lex.TUpper{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              strict.call(t, l, c, ok, o, ol, oc, kids, close, r2, name, path, outer, hot,
                                  Laws.strict_walk_counts(kids, name, path, strict.inner(hot, o, t),
                                    Bool.or(strict.inner(hot, o, t), Strict.seg_op(kids))),
                                  Laws.strict_walk_counts(r2, name, path, outer, hot))
                        case Tree.Leaf{x}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.Stmt{kind, kids, body}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NNil{}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NCons{x, y}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Leaf{x}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Group{open, kids, close}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Stmt{kind, kids, body}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.NNil{}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                case Lex.TDotted{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              strict.call(t, l, c, ok, o, ol, oc, kids, close, r2, name, path, outer, hot,
                                  Laws.strict_walk_counts(kids, name, path, strict.inner(hot, o, t),
                                    Bool.or(strict.inner(hot, o, t), Strict.seg_op(kids))),
                                  Laws.strict_walk_counts(r2, name, path, outer, hot))
                        case Tree.Leaf{x}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.Stmt{kind, kids, body}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NNil{}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NCons{x, y}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Leaf{x}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Group{open, kids, close}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Stmt{kind, kids, body}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.NNil{}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                case Lex.TWild{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              strict.call(t, l, c, ok, o, ol, oc, kids, close, r2, name, path, outer, hot,
                                  Laws.strict_walk_counts(kids, name, path, strict.inner(hot, o, t),
                                    Bool.or(strict.inner(hot, o, t), Strict.seg_op(kids))),
                                  Laws.strict_walk_counts(r2, name, path, outer, hot))
                        case Tree.Leaf{x}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.Stmt{kind, kids, body}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NNil{}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NCons{x, y}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Leaf{x}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Group{open, kids, close}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Stmt{kind, kids, body}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.NNil{}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                case Lex.TKey{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              strict.call(t, l, c, ok, o, ol, oc, kids, close, r2, name, path, outer, hot,
                                  Laws.strict_walk_counts(kids, name, path, strict.inner(hot, o, t),
                                    Bool.or(strict.inner(hot, o, t), Strict.seg_op(kids))),
                                  Laws.strict_walk_counts(r2, name, path, outer, hot))
                        case Tree.Leaf{x}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.Stmt{kind, kids, body}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NNil{}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NCons{x, y}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Leaf{x}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Group{open, kids, close}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Stmt{kind, kids, body}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.NNil{}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                case Lex.TNum{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              strict.call(t, l, c, ok, o, ol, oc, kids, close, r2, name, path, outer, hot,
                                  Laws.strict_walk_counts(kids, name, path, strict.inner(hot, o, t),
                                    Bool.or(strict.inner(hot, o, t), Strict.seg_op(kids))),
                                  Laws.strict_walk_counts(r2, name, path, outer, hot))
                        case Tree.Leaf{x}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.Stmt{kind, kids, body}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NNil{}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NCons{x, y}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Leaf{x}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Group{open, kids, close}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Stmt{kind, kids, body}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.NNil{}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                case Lex.TStr{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              strict.call(t, l, c, ok, o, ol, oc, kids, close, r2, name, path, outer, hot,
                                  Laws.strict_walk_counts(kids, name, path, strict.inner(hot, o, t),
                                    Bool.or(strict.inner(hot, o, t), Strict.seg_op(kids))),
                                  Laws.strict_walk_counts(r2, name, path, outer, hot))
                        case Tree.Leaf{x}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.Stmt{kind, kids, body}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NNil{}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NCons{x, y}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Leaf{x}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Group{open, kids, close}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Stmt{kind, kids, body}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.NNil{}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                case Lex.TChar{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              strict.call(t, l, c, ok, o, ol, oc, kids, close, r2, name, path, outer, hot,
                                  Laws.strict_walk_counts(kids, name, path, strict.inner(hot, o, t),
                                    Bool.or(strict.inner(hot, o, t), Strict.seg_op(kids))),
                                  Laws.strict_walk_counts(r2, name, path, outer, hot))
                        case Tree.Leaf{x}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.Stmt{kind, kids, body}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NNil{}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NCons{x, y}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Leaf{x}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Group{open, kids, close}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Stmt{kind, kids, body}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.NNil{}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                case Lex.TComment{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              strict.call(t, l, c, ok, o, ol, oc, kids, close, r2, name, path, outer, hot,
                                  Laws.strict_walk_counts(kids, name, path, strict.inner(hot, o, t),
                                    Bool.or(strict.inner(hot, o, t), Strict.seg_op(kids))),
                                  Laws.strict_walk_counts(r2, name, path, outer, hot))
                        case Tree.Leaf{x}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.Stmt{kind, kids, body}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NNil{}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NCons{x, y}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Leaf{x}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Group{open, kids, close}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Stmt{kind, kids, body}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.NNil{}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                case Lex.TSpace{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              strict.call(t, l, c, ok, o, ol, oc, kids, close, r2, name, path, outer, hot,
                                  Laws.strict_walk_counts(kids, name, path, strict.inner(hot, o, t),
                                    Bool.or(strict.inner(hot, o, t), Strict.seg_op(kids))),
                                  Laws.strict_walk_counts(r2, name, path, outer, hot))
                        case Tree.Leaf{x}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.Stmt{kind, kids, body}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NNil{}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NCons{x, y}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Leaf{x}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Group{open, kids, close}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Stmt{kind, kids, body}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.NNil{}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                case Lex.TNewline{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              strict.call(t, l, c, ok, o, ol, oc, kids, close, r2, name, path, outer, hot,
                                  Laws.strict_walk_counts(kids, name, path, strict.inner(hot, o, t),
                                    Bool.or(strict.inner(hot, o, t), Strict.seg_op(kids))),
                                  Laws.strict_walk_counts(r2, name, path, outer, hot))
                        case Tree.Leaf{x}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.Stmt{kind, kids, body}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NNil{}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NCons{x, y}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Leaf{x}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Group{open, kids, close}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Stmt{kind, kids, body}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.NNil{}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                case Lex.TOp{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              strict.call(t, l, c, ok, o, ol, oc, kids, close, r2, name, path, outer, hot,
                                  Laws.strict_walk_counts(kids, name, path, strict.inner(hot, o, t),
                                    Bool.or(strict.inner(hot, o, t), Strict.seg_op(kids))),
                                  Laws.strict_walk_counts(r2, name, path, outer, hot))
                        case Tree.Leaf{x}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.Stmt{kind, kids, body}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NNil{}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NCons{x, y}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Leaf{x}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Group{open, kids, close}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Stmt{kind, kids, body}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.NNil{}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                case Lex.TColon{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              strict.call(t, l, c, ok, o, ol, oc, kids, close, r2, name, path, outer, hot,
                                  Laws.strict_walk_counts(kids, name, path, strict.inner(hot, o, t),
                                    Bool.or(strict.inner(hot, o, t), Strict.seg_op(kids))),
                                  Laws.strict_walk_counts(r2, name, path, outer, hot))
                        case Tree.Leaf{x}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.Stmt{kind, kids, body}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NNil{}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NCons{x, y}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Leaf{x}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Group{open, kids, close}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Stmt{kind, kids, body}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.NNil{}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                case Lex.TEq{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              strict.call(t, l, c, ok, o, ol, oc, kids, close, r2, name, path, outer, hot,
                                  Laws.strict_walk_counts(kids, name, path, strict.inner(hot, o, t),
                                    Bool.or(strict.inner(hot, o, t), Strict.seg_op(kids))),
                                  Laws.strict_walk_counts(r2, name, path, outer, hot))
                        case Tree.Leaf{x}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.Stmt{kind, kids, body}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NNil{}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NCons{x, y}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Leaf{x}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Group{open, kids, close}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Stmt{kind, kids, body}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.NNil{}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                case Lex.TBind{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              strict.call(t, l, c, ok, o, ol, oc, kids, close, r2, name, path, outer, hot,
                                  Laws.strict_walk_counts(kids, name, path, strict.inner(hot, o, t),
                                    Bool.or(strict.inner(hot, o, t), Strict.seg_op(kids))),
                                  Laws.strict_walk_counts(r2, name, path, outer, hot))
                        case Tree.Leaf{x}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.Stmt{kind, kids, body}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NNil{}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NCons{x, y}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Leaf{x}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Group{open, kids, close}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Stmt{kind, kids, body}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.NNil{}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                case Lex.TArrow{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              strict.call(t, l, c, ok, o, ol, oc, kids, close, r2, name, path, outer, hot,
                                  Laws.strict_walk_counts(kids, name, path, strict.inner(hot, o, t),
                                    Bool.or(strict.inner(hot, o, t), Strict.seg_op(kids))),
                                  Laws.strict_walk_counts(r2, name, path, outer, hot))
                        case Tree.Leaf{x}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.Stmt{kind, kids, body}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NNil{}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NCons{x, y}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Leaf{x}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Group{open, kids, close}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Stmt{kind, kids, body}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.NNil{}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                case Lex.TLam{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              strict.lam(rest, name, path, outer, Laws.strict_walk_counts(rest, name, path, outer,
                                Strict.seg_op(rest)))
                        case Tree.Leaf{x}:
                          strict.lam(rest, name, path, outer, Laws.strict_walk_counts(rest, name, path, outer,
                            Strict.seg_op(rest)))
                        case Tree.Stmt{kind, kids, body}:
                          strict.lam(rest, name, path, outer, Laws.strict_walk_counts(rest, name, path, outer,
                            Strict.seg_op(rest)))
                        case Tree.NNil{}:
                          strict.lam(rest, name, path, outer, Laws.strict_walk_counts(rest, name, path, outer,
                            Strict.seg_op(rest)))
                        case Tree.NCons{x, y}:
                          strict.lam(rest, name, path, outer, Laws.strict_walk_counts(rest, name, path, outer,
                            Strict.seg_op(rest)))
                    case Tree.Leaf{x}:
                      strict.lam(rest, name, path, outer, Laws.strict_walk_counts(rest, name, path, outer,
                        Strict.seg_op(rest)))
                    case Tree.Group{open, kids, close}:
                      strict.lam(rest, name, path, outer, Laws.strict_walk_counts(rest, name, path, outer,
                        Strict.seg_op(rest)))
                    case Tree.Stmt{kind, kids, body}:
                      strict.lam(rest, name, path, outer, Laws.strict_walk_counts(rest, name, path, outer,
                        Strict.seg_op(rest)))
                    case Tree.NNil{}:
                      strict.lam(rest, name, path, outer, Laws.strict_walk_counts(rest, name, path, outer,
                        Strict.seg_op(rest)))
                case Lex.TAll{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              strict.call(t, l, c, ok, o, ol, oc, kids, close, r2, name, path, outer, hot,
                                  Laws.strict_walk_counts(kids, name, path, strict.inner(hot, o, t),
                                    Bool.or(strict.inner(hot, o, t), Strict.seg_op(kids))),
                                  Laws.strict_walk_counts(r2, name, path, outer, hot))
                        case Tree.Leaf{x}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.Stmt{kind, kids, body}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NNil{}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NCons{x, y}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Leaf{x}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Group{open, kids, close}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Stmt{kind, kids, body}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.NNil{}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                case Lex.TAmp{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              strict.call(t, l, c, ok, o, ol, oc, kids, close, r2, name, path, outer, hot,
                                  Laws.strict_walk_counts(kids, name, path, strict.inner(hot, o, t),
                                    Bool.or(strict.inner(hot, o, t), Strict.seg_op(kids))),
                                  Laws.strict_walk_counts(r2, name, path, outer, hot))
                        case Tree.Leaf{x}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.Stmt{kind, kids, body}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NNil{}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NCons{x, y}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Leaf{x}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Group{open, kids, close}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Stmt{kind, kids, body}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.NNil{}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                case Lex.TOpen{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              strict.call(t, l, c, ok, o, ol, oc, kids, close, r2, name, path, outer, hot,
                                  Laws.strict_walk_counts(kids, name, path, strict.inner(hot, o, t),
                                    Bool.or(strict.inner(hot, o, t), Strict.seg_op(kids))),
                                  Laws.strict_walk_counts(r2, name, path, outer, hot))
                        case Tree.Leaf{x}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.Stmt{kind, kids, body}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NNil{}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NCons{x, y}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Leaf{x}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Group{open, kids, close}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Stmt{kind, kids, body}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.NNil{}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                case Lex.TClose{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              strict.call(t, l, c, ok, o, ol, oc, kids, close, r2, name, path, outer, hot,
                                  Laws.strict_walk_counts(kids, name, path, strict.inner(hot, o, t),
                                    Bool.or(strict.inner(hot, o, t), Strict.seg_op(kids))),
                                  Laws.strict_walk_counts(r2, name, path, outer, hot))
                        case Tree.Leaf{x}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.Stmt{kind, kids, body}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NNil{}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                        case Tree.NCons{x, y}:
                          Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Leaf{x}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Group{open, kids, close}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.Stmt{kind, kids, body}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                    case Tree.NNil{}:
                      Laws.strict_walk_counts(rest, name, path, outer, hot)
                case Lex.TComma{}:
                  match rest:
                    case Tree.NCons{h2, +r2}:
                      match h2:
                        case Tree.Group{open, +kids, close}:
                          match open:
                            case Lex.Tok{ok, +o, ol, oc}:
                              strict.comma(rest, name, path, outer, Laws.strict_walk_counts(rest, name, path, outer,
                                Bool.or(outer, Strict.seg_op(rest))))
                        case Tree.Leaf{x}:
                          strict.comma(rest, name, path, outer, Laws.strict_walk_counts(rest, name, path, outer,
                            Bool.or(outer, Strict.seg_op(rest))))
                        case Tree.Stmt{kind, kids, body}:
                          strict.comma(rest, name, path, outer, Laws.strict_walk_counts(rest, name, path, outer,
                            Bool.or(outer, Strict.seg_op(rest))))
                        case Tree.NNil{}:
                          strict.comma(rest, name, path, outer, Laws.strict_walk_counts(rest, name, path, outer,
                            Bool.or(outer, Strict.seg_op(rest))))
                        case Tree.NCons{x, y}:
                          strict.comma(rest, name, path, outer, Laws.strict_walk_counts(rest, name, path, outer,
                            Bool.or(outer, Strict.seg_op(rest))))
                    case Tree.Leaf{x}:
                      strict.comma(rest, name, path, outer, Laws.strict_walk_counts(rest, name, path, outer,
                        Bool.or(outer, Strict.seg_op(rest))))
                    case Tree.Group{open, kids, close}:
                      strict.comma(rest, name, path, outer, Laws.strict_walk_counts(rest, name, path, outer,
                        Bool.or(outer, Strict.seg_op(rest))))
                    case Tree.Stmt{kind, kids, body}:
                      strict.comma(rest, name, path, outer, Laws.strict_walk_counts(rest, name, path, outer,
                        Bool.or(outer, Strict.seg_op(rest))))
                    case Tree.NNil{}:
                      strict.comma(rest, name, path, outer, Laws.strict_walk_counts(rest, name, path, outer,
                        Bool.or(outer, Strict.seg_op(rest))))
        case Tree.Group{open, +kids, close}:
          +fr = Strict.walk(rest, name, path, outer, hot)
          +hk = Bool.or(hot, Strict.seg_op(kids))
          M2.pick.join(Strict.walk(kids, name, path, hot, hk), List.append(&2, F.Finding, fr, Nil{}),
            Laws.strict.count(kids, name, hot, Bool.or(hot, Laws.strict.ops(kids))), Laws.strict.count(rest, name,
              outer, hot),
            strict.hot(kids, name, path, hot, hk, Bool.or(hot, Laws.strict.ops(kids)),
              Equal.cong(Bool, Bool, x => Bool.or(hot, x), Strict.seg_op(kids), Laws.strict.ops(kids),
                strict.seg(kids)),
              Laws.strict_walk_counts(kids, name, path, hot, hk)),
            M2.pick.last(fr, Laws.strict.count(rest, name, outer, hot), Laws.strict_walk_counts(rest, name, path, outer,
              hot)))
        case Tree.Stmt{kind, +kids, +body}:
          +fb = Strict.walk(body, name, path, False{}, False{})
          +fr = Strict.walk(rest, name, path, outer, hot)
          +cb = Laws.strict.count(body, name, False{}, False{})
          +cr = Laws.strict.count(rest, name, outer, hot)
          M2.pick.join(Strict.walk(kids, name, path, False{}, Strict.seg_op(kids)),
            List.append(&2, F.Finding, fb, List.append(&2, F.Finding, fr, Nil{})),
            Laws.strict.count(kids, name, False{}, Laws.strict.ops(kids)), Nat.add(cb, cr),
            strict.hot(kids, name, path, False{}, Strict.seg_op(kids), Laws.strict.ops(kids), strict.seg(kids),
              Laws.strict_walk_counts(kids, name, path, False{}, Strict.seg_op(kids))),
            M2.pick.join(fb, List.append(&2, F.Finding, fr, Nil{}), cb, cr, Laws.strict_walk_counts(body, name, path,
              False{}, False{}),
              M2.pick.last(fr, cr, Laws.strict_walk_counts(rest, name, path, outer, hot))))
        case Tree.NNil{}:
          Laws.strict_walk_counts(rest, name, path, outer, hot)
        case Tree.NCons{x, y}:
          Laws.strict_walk_counts(rest, name, path, outer, hot)
    case Tree.Leaf{tok}:
      {==}
    case Tree.Group{open, kids, close}:
      {==}
    case Tree.Stmt{kind, kids, body}:
      {==}
    case Tree.NNil{}:
      {==}

# one def's findings, exempt or walked
law strict.stop:
  for +b: Bool
  for +body: Tree.Node
  for +name: String
  for +path: String
  {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, b, [], _u => Strict.walk(body, name, path, False{},
    False{})))
    == Bool.pick(Nat, b, 0n, Laws.strict.count(body, name, False{}, False{})) : Nat}

def strict.stop(b, body, name, path):
  match b:
    case True{}:
      {==}
    case False{}:
      Laws.strict_walk_counts(body, name, path, False{}, False{})

# strict's def walk: the findings gathered so far, then each def's
law strict.go:
  for ds: List<&2, Calls.Def>
  for +path: String
  for +acc: List<&2, List<&2, F.Finding>>
  {List.length(&2, F.Finding, Strict.check.go(ds, path, acc)) == M2.pick.sum(acc, Laws.strict.defs(ds, path)) : Nat}

def strict.go(ds, path, acc):
  match ds:
    case Nil{}:
      M2.pick.rev(acc, Nil{})
    case Con{Calls.Def{+name, +sig, +body}, +rest}:
      +x = Lazy.stop(List<&2, F.Finding>, Calls.exempt(path, sig), [], _u => Strict.walk(body, name, path, False{},
        False{}))
      +cb = Bool.pick(Nat, Calls.exempt(path, sig), 0n, Laws.strict.count(body, name, False{}, False{}))
      Equal.trans(Nat, List.length(&2, F.Finding, Strict.check.go(rest, path, x <> acc)),
        M2.pick.sum(acc, Nat.add(List.length(&2, F.Finding, x), Laws.strict.defs(rest, path))),
        M2.pick.sum(acc, Nat.add(cb, Laws.strict.defs(rest, path))),
        strict.go(rest, path, x <> acc),
        Equal.cong(Nat, Nat, n => M2.pick.sum(acc, Nat.add(n, Laws.strict.defs(rest, path))),
          List.length(&2, F.Finding, x), cb, strict.stop(Calls.exempt(path, sig), body, name, path)))

def Laws.strict_counts(path, _text, _toks, tree, _bound, _items):
  strict.go(Calls.defs(tree), path, Nil{})
