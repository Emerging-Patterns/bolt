# proofs of laws/InertConcatCont.bend
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/lazy/lazy.bend as Lazy
import ../src/syntax/tree.bend as Tree
import ../src/rules/calls.bend as Calls
import ../src/rules/suspicious/concat.bend as Concat
import ../laws/InertConcatCont.bend as Laws
import ../laws/defs/InertText.bend as D1
import ./lemmas/InertTextFacts.bend as M1
import ./lemmas/CarriedSearch.bend as CS
import ./CodeRulesIgnoreCommentsAndStrings.bend as P

# The continuation half reads strings nowhere: a token's text is compared
# with the def's function-typed parameters, every one a name the lexer never
# starts with `"` or `#`, and an argument's appends are read as the
# self-call half reads them (P.inert.concat.seen). What it reads of the
# signature and the body, the continuations and the reportable parameters,
# is names and kinds, which reading that way keeps.

# no name in the list starts with `"` or `#`
def cont.plain(xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      Bool.and(Bool.not(D1.inert.marked(h)), cont.plain(t))

# a marked char and an unmarked one never compare EQ, the unmarked first
law cont.differ:
  for c: Cmp
  for +x: U32
  for +y: U32
  for ec: {U32.cmp(y, x) == c : Cmp}
  for ex: {D1.inert.mark(Chr{x}) == True{} : Bool}
  for ey: {D1.inert.mark(Chr{y}) == False{} : Bool}
  {Cmp.is_eq(c) == False{} : Bool}

def cont.differ(c, x, y, ec, ex, ey):
  match c:
    case LT{}: {==}
    case GT{}: {==}
    case EQ{}:
      +my = Equal.trans(Bool, D1.inert.mark(Chr{y}), D1.inert.mark(Chr{x}), True{},
        Equal.cong(U32, Bool, z => D1.inert.mark(Chr{z}), y, x, M1.inert.u32_eq(y, x, ec)), ex)
      Empty.absurd({Cmp.is_eq(EQ{}) == False{} : Bool}, M1.inert.false_true(Equal.trans(Bool, False{},
        D1.inert.mark(Chr{y}), True{}, Equal.sym(Bool, D1.inert.mark(Chr{y}), False{}, ey), my)))

# an unmarked text is never equal to one with a marked first char
law cont.neq.con:
  for h: Char
  for r: String
  for y: Char
  for ys: String
  for et: {D1.inert.mark(h) == True{} : Bool}
  for ex: {D1.inert.mark(y) == False{} : Bool}
  {String.eq(SCon{y, ys}, SCon{h, r}) == False{} : Bool}

def cont.neq.con(h, r, y, ys, et, ex):
  match h y:
    case Chr{+a} Chr{+b}:
      M1.inert.fin_false(U32.cmp(b, a), ys, r, cont.differ(U32.cmp(b, a), a, b, {==}, et, ex))

# an unmarked text is never equal to a marked one
law cont.neq:
  for x: String
  for t: String
  for ex: {D1.inert.marked(x) == False{} : Bool}
  for et: {D1.inert.marked(t) == True{} : Bool}
  {String.eq(x, t) == False{} : Bool}

def cont.neq(x, t, ex, et):
  match x t:
    case x SNil{}: Empty.absurd({String.eq(x, SNil{}) == False{} : Bool}, M1.inert.false_true(et))
    case SNil{} SCon{Chr{_a}, r}: {==}
    case SCon{y, ys} SCon{h, r}: cont.neq.con(h, r, y, ys, et, ex)

# an unmarked text compares with a token's text read that way as it did
law cont.eq_keep:
  for b: Bool
  for +t: String
  for +x: String
  for +ef: {D1.inert.fits.go(b, t) == True{} : Bool}
  for +ex: {D1.inert.marked(x) == False{} : Bool}
  {String.eq(x, D1.inert.keep(b, t)) == String.eq(x, t) : Bool}

def cont.eq_keep(b, t, x, ef, ex):
  match b:
    case False{}: {==}
    case True{}:
      Equal.trans(Bool, String.eq(x, D1.inert.cut(t)), False{}, String.eq(x, t),
        cont.neq(x, D1.inert.cut(t), ex, M1.inert.cut_marked(t, ef)),
        Equal.sym(Bool, String.eq(x, t), False{}, cont.neq(x, t, ex, ef)))

# a membership step whose head test and rest read as they did reads as it did
law cont.any:
  for -c1: Bool
  for -c2: Bool
  for -x1: Bool
  for -x2: Bool
  for ec: {c1 == c2 : Bool}
  for ex: {x1 == x2 : Bool}
  {List.any.if(_u => x1, c1) == List.any.if(_v => x2, c2) : Bool}

def cont.any(c1, _c2, x1, x2, ec, ex):
  %ec : {List.any.if(_u => x1, c1) == List.any.if(_v => x2, _) : Bool}
  %ex : {List.any.if(_u => x1, c1) == List.any.if(_v => _, c1) : Bool}
  {==}

# a token's text read that way is among plain names exactly when it was
law cont.mem:
  for xs: List<&2, String>
  for +b: Bool
  for +t: String
  for +ef: {D1.inert.fits.go(b, t) == True{} : Bool}
  for +ep: {cont.plain(xs) == True{} : Bool}
  {List.contains(~String, ~String.eq, xs, D1.inert.keep(b, t)) == List.contains(~String, ~String.eq, xs, t) : Bool}

def cont.mem(xs, b, t, ef, ep):
  match xs:
    case Nil{}: {==}
    case Con{+h, +r}:
      +mh = P.inert.not_true(D1.inert.marked(h), M1.inert.and_l(Bool.not(D1.inert.marked(h)), cont.plain(r), ep))
      +kt = D1.inert.keep(b, t)
      cont.any(String.eq(h, kt), String.eq(h, t), List.contains(~String, ~String.eq, r, kt),
        List.contains(~String, ~String.eq, r, t), cont.eq_keep(b, t, h, ef, mh),
        cont.mem(r, b, t, ef, M1.inert.and_r(Bool.not(D1.inert.marked(h)), cont.plain(r), ep)))

# a parameter's name, from a chain the lexer made, is plain
law cont.pname:
  for pp: Tree.Node
  for +e: {D1.inert.ok(pp) == True{} : Bool}
  {Bool.not(D1.inert.marked(Calls.param_name(pp))) == True{} : Bool}

def cont.pname(pp, e):
  match pp:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{k, +t, +l, +c}:
              match k:
                case Lex.TName{}: M1.inert.and_l(Bool.not(D1.inert.marked(t)), D1.inert.ok(rest), e)
                case Lex.TUpper{}: cont.pname(rest, P.inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TUpper{}, t, l, c}}, rest, e))
                case Lex.TDotted{}: cont.pname(rest, P.inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TDotted{}, t, l, c}}, rest, e))
                case Lex.TWild{}: cont.pname(rest, P.inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TWild{}, t, l, c}}, rest, e))
                case Lex.TKey{}: cont.pname(rest, P.inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TKey{}, t, l, c}}, rest, e))
                case Lex.TNum{}: cont.pname(rest, P.inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TNum{}, t, l, c}}, rest, e))
                case Lex.TStr{}: cont.pname(rest, P.inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TStr{}, t, l, c}}, rest, e))
                case Lex.TChar{}: cont.pname(rest, P.inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TChar{}, t, l, c}}, rest, e))
                case Lex.TComment{}: cont.pname(rest,
                  P.inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TComment{}, t, l, c}}, rest, e))
                case Lex.TSpace{}: cont.pname(rest, P.inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TSpace{}, t, l, c}}, rest, e))
                case Lex.TNewline{}: cont.pname(rest,
                  P.inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TNewline{}, t, l, c}}, rest, e))
                case Lex.TOp{}: cont.pname(rest, P.inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TOp{}, t, l, c}}, rest, e))
                case Lex.TColon{}: {==}
                case Lex.TEq{}: cont.pname(rest, P.inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TEq{}, t, l, c}}, rest, e))
                case Lex.TBind{}: cont.pname(rest, P.inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TBind{}, t, l, c}}, rest, e))
                case Lex.TArrow{}: cont.pname(rest, P.inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TArrow{}, t, l, c}}, rest, e))
                case Lex.TLam{}: cont.pname(rest, P.inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TLam{}, t, l, c}}, rest, e))
                case Lex.TAll{}: cont.pname(rest, P.inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TAll{}, t, l, c}}, rest, e))
                case Lex.TAmp{}: cont.pname(rest, P.inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TAmp{}, t, l, c}}, rest, e))
                case Lex.TOpen{}: cont.pname(rest, P.inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TOpen{}, t, l, c}}, rest, e))
                case Lex.TClose{}: cont.pname(rest, P.inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TClose{}, t, l, c}}, rest, e))
                case Lex.TComma{}: cont.pname(rest, P.inert.ok_t(Tree.Leaf{Lex.Tok{Lex.TComma{}, t, l, c}}, rest, e))
        case Tree.Group{o, +gk, +cl}: cont.pname(rest, P.inert.ok_t(Tree.Group{o, gk, cl}, rest, e))
        case Tree.Stmt{+sk, +sks, +sb}: cont.pname(rest, P.inert.ok_t(Tree.Stmt{sk, sks, sb}, rest, e))
        case Tree.NNil{}: cont.pname(rest, P.inert.ok_t(Tree.NNil{}, rest, e))
        case Tree.NCons{+x, +y}: cont.pname(rest, P.inert.ok_t(Tree.NCons{x, y}, rest, e))
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# a pick between two fitting trees fits
law cont.ok.pick:
  for b: Bool
  for -x: Tree.Node
  for -y: Tree.Node
  for ex: {D1.inert.ok(x) == True{} : Bool}
  for ey: {D1.inert.ok(y) == True{} : Bool}
  {D1.inert.ok(Bool.pick(Tree.Node, b, x, y)) == True{} : Bool}

def cont.ok.pick(b, _x, _y, ex, ey):
  match b:
    case True{}: ex
    case False{}: ey

# a signature's parameters, from a signature the lexer made, fit
law cont.ok.params.of:
  for sig: Tree.Node
  for +e: {D1.inert.ok(sig) == True{} : Bool}
  {D1.inert.ok(Calls.params.of(sig)) == True{} : Bool}

def cont.ok.params.of(sig, e):
  match sig:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Group{o, +kids, +cl}:
          match o:
            case Lex.Tok{+k, +ot, +l, +c}:
              +g = {Tree.Group{Lex.Tok{k, ot, l, c}, kids, cl} : Tree.Node}
              %Equal.sym(Tree.Node, Calls.params.of(Tree.NCons{g, rest}),
                Bool.pick(Tree.Node, String.eq(ot, "("), kids, Calls.params.of(rest)),
                CS.cs.params.of(k, ot, l, c, kids, cl, rest)) : {D1.inert.ok(_) == True{} : Bool}
              cont.ok.pick(String.eq(ot, "("), kids, Calls.params.of(rest), P.inert.ok_h(g, rest, e),
                cont.ok.params.of(rest, P.inert.ok_t(g, rest, e)))
        case Tree.Leaf{+tok}: cont.ok.params.of(rest, P.inert.ok_t(Tree.Leaf{tok}, rest, e))
        case Tree.Stmt{+sk, +sks, +sb}: cont.ok.params.of(rest, P.inert.ok_t(Tree.Stmt{sk, sks, sb}, rest, e))
        case Tree.NNil{}: cont.ok.params.of(rest, P.inert.ok_t(Tree.NNil{}, rest, e))
        case Tree.NCons{+x, +y}: cont.ok.params.of(rest, P.inert.ok_t(Tree.NCons{x, y}, rest, e))
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# a pushed name keeps the names plain when it is plain
law cont.plain.pick:
  for c: Bool
  for +n: String
  for +acc: List<&2, String>
  for en: {Bool.not(D1.inert.marked(n)) == True{} : Bool}
  for ea: {cont.plain(acc) == True{} : Bool}
  {cont.plain(Bool.pick(List<&2, String>, c, n <> acc, acc)) == True{} : Bool}

def cont.plain.pick(c, n, acc, en, ea):
  match c:
    case True{}: M1.inert.and_both(Bool.not(D1.inert.marked(n)), cont.plain(acc), en, ea)
    case False{}: ea

# the continuations of fitting parameters are plain
law cont.plain.go:
  for ps: List<&2, Tree.Node>
  for +acc: List<&2, String>
  for +ep: {P.inert.noks(ps) == True{} : Bool}
  for +ea: {cont.plain(acc) == True{} : Bool}
  {cont.plain(Concat.conts.go(ps, acc)) == True{} : Bool}

def cont.plain.go(ps, acc, ep, ea):
  match ps:
    case Nil{}: ea
    case Con{+p, +rest}:
      cont.plain.go(rest, Bool.pick(List<&2, String>, Calls.has_arrow(p), Calls.param_name(p) <> acc, acc),
        M1.inert.and_r(D1.inert.ok(p), P.inert.noks(rest), ep),
        cont.plain.pick(Calls.has_arrow(p), Calls.param_name(p), acc,
          cont.pname(p, M1.inert.and_l(D1.inert.ok(p), P.inert.noks(rest), ep)), ea))

# the continuations of a signature the lexer made are plain
law cont.plain.conts:
  for +sig: Tree.Node
  for +e: {D1.inert.ok(sig) == True{} : Bool}
  {cont.plain(Concat.conts(sig)) == True{} : Bool}

def cont.plain.conts(sig, e):
  cont.plain.go(Calls.params(sig), [],
    P.inert.ok.args.go(Calls.params.of(sig), Tree.NNil{}, [], cont.ok.params.of(sig, e), {==}, {==}), {==})

# how often a name is read, the tree read that way: only names are counted
law cont.uses:
  for nn: Tree.Node
  for +name: String
  {Concat.uses(D1.inert.node(nn), name) == Concat.uses(nn, name) : Nat}

def cont.uses(nn, name):
  match nn:
    case Tree.NCons{+h, +t}:
      %cont.uses(h, name) : {Nat.add(Concat.uses(D1.inert.node(h), name), Concat.uses(D1.inert.node(t), name))
        == Nat.add(_, Concat.uses(t, name)) : Nat}
      %cont.uses(t, name) : {Nat.add(Concat.uses(D1.inert.node(h), name), Concat.uses(D1.inert.node(t), name))
        == Nat.add(Concat.uses(D1.inert.node(h), name), _) : Nat}
      {==}
    case Tree.Group{o, +kids, cl}: cont.uses(kids, name)
    case Tree.Stmt{sk, +kids, +body}:
      %cont.uses(kids, name) : {Nat.add(Concat.uses(D1.inert.node(kids), name),
        Concat.uses(D1.inert.node(body), name)) == Nat.add(_, Concat.uses(body, name)) : Nat}
      %cont.uses(body, name) : {Nat.add(Concat.uses(D1.inert.node(kids), name),
        Concat.uses(D1.inert.node(body), name)) == Nat.add(Concat.uses(D1.inert.node(kids), name), _) : Nat}
      {==}
    case Tree.Leaf{tok}:
      match tok:
        case Lex.Tok{k, t, l, c}:
          match k:
            case Lex.TName{}: {==}
            case Lex.TUpper{}: {==}
            case Lex.TDotted{}: {==}
            case Lex.TWild{}: {==}
            case Lex.TKey{}: {==}
            case Lex.TNum{}: {==}
            case Lex.TStr{}: {==}
            case Lex.TChar{}: {==}
            case Lex.TComment{}: {==}
            case Lex.TSpace{}: {==}
            case Lex.TNewline{}: {==}
            case Lex.TOp{}: {==}
            case Lex.TColon{}: {==}
            case Lex.TEq{}: {==}
            case Lex.TBind{}: {==}
            case Lex.TArrow{}: {==}
            case Lex.TLam{}: {==}
            case Lex.TAll{}: {==}
            case Lex.TAmp{}: {==}
            case Lex.TOpen{}: {==}
            case Lex.TClose{}: {==}
            case Lex.TComma{}: {==}
    case Tree.NNil{}: {==}

# a parameter read that way is `+` as it was: only an operator's text is read
law cont.plus:
  for pp: Tree.Node
  {Concat.plus(D1.inert.node(pp)) == Concat.plus(pp) : Bool}

def cont.plus(pp):
  match pp:
    case Tree.NCons{h, rest}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{k, t, l, c}:
              match k:
                case Lex.TName{}: {==}
                case Lex.TUpper{}: {==}
                case Lex.TDotted{}: {==}
                case Lex.TWild{}: {==}
                case Lex.TKey{}: {==}
                case Lex.TNum{}: {==}
                case Lex.TStr{}: {==}
                case Lex.TChar{}: {==}
                case Lex.TComment{}: {==}
                case Lex.TSpace{}: {==}
                case Lex.TNewline{}: {==}
                case Lex.TOp{}: {==}
                case Lex.TColon{}: {==}
                case Lex.TEq{}: {==}
                case Lex.TBind{}: {==}
                case Lex.TArrow{}: {==}
                case Lex.TLam{}: {==}
                case Lex.TAll{}: {==}
                case Lex.TAmp{}: {==}
                case Lex.TOpen{}: {==}
                case Lex.TClose{}: {==}
                case Lex.TComma{}: {==}
        case Tree.Group{o, gk, cl}: {==}
        case Tree.Stmt{sk, sks, sb}: {==}
        case Tree.NNil{}: {==}
        case Tree.NCons{x, y}: {==}
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# one parameter's push onto the reportable ones, it and the body read that
# way
law cont.accs.step:
  for +p: Tree.Node
  for +body: Tree.Node
  for +acc: List<&2, String>
  {Bool.pick(List<&2, String>, Concat.keep(Concat.plus(D1.inert.node(p)), Concat.uses(D1.inert.node(body),
    Calls.param_name(D1.inert.node(p)))), Calls.param_name(D1.inert.node(p)) <> acc, acc)
    == Bool.pick(List<&2, String>, Concat.keep(Concat.plus(p), Concat.uses(body, Calls.param_name(p))),
      Calls.param_name(p) <> acc, acc) : List<&2, String>}

def cont.accs.step(p, body, acc):
  +ip = D1.inert.node(p)
  +ib = D1.inert.node(body)
  +ai = Bool.pick(List<&2, String>, Concat.keep(Concat.plus(ip), Concat.uses(ib, Calls.param_name(ip))),
    Calls.param_name(ip) <> acc, acc)
  %P.inert.param_name(p) : {ai == Bool.pick(List<&2, String>, Concat.keep(Concat.plus(p), Concat.uses(body, _)),
    _ <> acc, acc) : List<&2, String>}
  %cont.plus(p) : {ai == Bool.pick(List<&2, String>, Concat.keep(_, Concat.uses(body, Calls.param_name(ip))),
    Calls.param_name(ip) <> acc, acc) : List<&2, String>}
  %cont.uses(body, Calls.param_name(ip)) : {ai == Bool.pick(List<&2, String>, Concat.keep(Concat.plus(ip), _),
    Calls.param_name(ip) <> acc, acc) : List<&2, String>}
  {==}

# the reportable parameters, the chains and the body read that way
law cont.accs.go:
  for ps: List<&2, Tree.Node>
  for +body: Tree.Node
  for +acc: List<&2, String>
  {Concat.accs.go(P.inert.nodes(ps), D1.inert.node(body), acc) == Concat.accs.go(ps, body, acc) : List<&2, String>}

def cont.accs.go(ps, body, acc):
  match ps:
    case Nil{}: {==}
    case Con{+p, +rest}:
      +ip = D1.inert.node(p)
      +ib = D1.inert.node(body)
      +ai = Bool.pick(List<&2, String>, Concat.keep(Concat.plus(ip), Concat.uses(ib, Calls.param_name(ip))),
        Calls.param_name(ip) <> acc, acc)
      +ao = Bool.pick(List<&2, String>, Concat.keep(Concat.plus(p), Concat.uses(body, Calls.param_name(p))),
        Calls.param_name(p) <> acc, acc)
      Equal.trans(List<&2, String>, Concat.accs.go(P.inert.nodes(rest), ib, ai), Concat.accs.go(P.inert.nodes(rest),
        ib, ao), Concat.accs.go(rest, body, ao),
        Equal.cong(List<&2, String>, List<&2, String>, z => Concat.accs.go(P.inert.nodes(rest), ib, z), ai, ao,
          cont.accs.step(p, body, acc)),
        cont.accs.go(rest, body, ao))

# a def's reportable parameters, its signature and body read that way
law cont.accs:
  for +sig: Tree.Node
  for +body: Tree.Node
  {Concat.accs(D1.inert.node(sig), D1.inert.node(body)) == Concat.accs(sig, body) : List<&2, String>}

def cont.accs(sig, body):
  +pp = Calls.params.of(sig)
  +ib = D1.inert.node(body)
  +lhs = Concat.accs(D1.inert.node(sig), ib)
  %cont.accs.go(Calls.args(pp), body, []) : {lhs == _ : List<&2, String>}
  %P.inert.args(pp) : {lhs == Concat.accs.go(_, ib, []) : List<&2, String>}
  %P.inert.params.of(sig) : {lhs == Concat.accs.go(Calls.args(_), ib, []) : List<&2, String>}
  {==}

# one parameter's push onto the continuations, read that way
law cont.conts.step:
  for +p: Tree.Node
  for +acc: List<&2, String>
  {Bool.pick(List<&2, String>, Calls.has_arrow(D1.inert.node(p)), Calls.param_name(D1.inert.node(p)) <> acc, acc)
    == Bool.pick(List<&2, String>, Calls.has_arrow(p), Calls.param_name(p) <> acc, acc) : List<&2, String>}

def cont.conts.step(p, acc):
  +ip = D1.inert.node(p)
  +ai = Bool.pick(List<&2, String>, Calls.has_arrow(ip), Calls.param_name(ip) <> acc, acc)
  %P.inert.param_name(p) : {ai == Bool.pick(List<&2, String>, Calls.has_arrow(p), _ <> acc, acc) : List<&2, String>}
  %P.inert.has_arrow(p) : {ai == Bool.pick(List<&2, String>, _, Calls.param_name(ip) <> acc, acc) : List<&2, String>}
  {==}

# the continuations, the chains read that way
law cont.conts.go:
  for ps: List<&2, Tree.Node>
  for +acc: List<&2, String>
  {Concat.conts.go(P.inert.nodes(ps), acc) == Concat.conts.go(ps, acc) : List<&2, String>}

def cont.conts.go(ps, acc):
  match ps:
    case Nil{}: {==}
    case Con{+p, +rest}:
      +ip = D1.inert.node(p)
      +ai = Bool.pick(List<&2, String>, Calls.has_arrow(ip), Calls.param_name(ip) <> acc, acc)
      +ao = Bool.pick(List<&2, String>, Calls.has_arrow(p), Calls.param_name(p) <> acc, acc)
      Equal.trans(List<&2, String>, Concat.conts.go(P.inert.nodes(rest), ai), Concat.conts.go(P.inert.nodes(rest),
        ao), Concat.conts.go(rest, ao),
        Equal.cong(List<&2, String>, List<&2, String>, z => Concat.conts.go(P.inert.nodes(rest), z), ai, ao,
          cont.conts.step(p, acc)),
        cont.conts.go(rest, ao))

# a def's continuations, its signature read that way
law cont.conts:
  for +sig: Tree.Node
  {Concat.conts(D1.inert.node(sig)) == Concat.conts(sig) : List<&2, String>}

def cont.conts(sig):
  +pp = Calls.params.of(sig)
  +lhs = Concat.conts(D1.inert.node(sig))
  %cont.conts.go(Calls.args(pp), []) : {lhs == _ : List<&2, String>}
  %P.inert.args(pp) : {lhs == Concat.conts.go(_, []) : List<&2, String>}
  %P.inert.params.of(sig) : {lhs == Concat.conts.go(Calls.args(_), []) : List<&2, String>}
  {==}

# a continuation call's arguments read that way hit as they did
law cont.hits:
  for as: List<&2, Tree.Node>
  for +accs: List<&2, String>
  for +lets: List<&2, Concat.Let>
  for +path: String
  for +acc: List<&2, F.Finding>
  for +e: {P.inert.noks(as) == True{} : Bool}
  {Concat.hits.cont(P.inert.nodes(as), accs, lets, path, acc) == Concat.hits.cont(as, accs, lets, path, acc)
    : List<&2, F.Finding>}

def cont.hits(as, accs, lets, path, acc, e):
  match as:
    case Nil{}: {==}
    case Con{+a, +rest}:
      +nx = Concat.hit.cont(Concat.seen(D1.inert.node(a), lets), accs, path, acc)
      %P.inert.concat.seen(a, lets, M1.inert.and_l(D1.inert.ok(a), P.inert.noks(rest), e)) :
        {Concat.hits.cont(P.inert.nodes(rest), accs, lets, path, nx)
          == Concat.hits.cont(rest, accs, lets, path, Concat.hit.cont(_, accs, path, acc)) : List<&2, F.Finding>}
      cont.hits(rest, accs, lets, path, nx, M1.inert.and_r(D1.inert.ok(a), P.inert.noks(rest), e))

# a name then a group: the continuation call's arguments, the group and the
# rest walked as they were
law cont.lg:
  for +b: Bool
  for +t: String
  for +o: String
  for +conts: List<&2, String>
  for +accs: List<&2, String>
  for +lets: List<&2, Concat.Let>
  for +path: String
  for +kids: Tree.Node
  for +r2: Tree.Node
  for +ef: {D1.inert.fits.go(b, t) == True{} : Bool}
  for +ep: {cont.plain(conts) == True{} : Bool}
  for +ek: {D1.inert.ok(kids) == True{} : Bool}
  for ik: {Concat.cwalk(D1.inert.node(kids), conts, accs, lets, path) == Concat.cwalk(kids, conts, accs, lets, path)
    : List<&2, F.Finding>}
  for ir: {Concat.cwalk(D1.inert.node(r2), conts, accs, lets, path) == Concat.cwalk(r2, conts, accs, lets, path)
    : List<&2, F.Finding>}
  {List.concat(&2, F.Finding, [Lazy.stop(List<&2, F.Finding>, Bool.not(Bool.and(String.eq(o, "("),
    List.contains(~String, ~String.eq, conts, D1.inert.keep(b, t)))), [],
      _u => Concat.hits.cont(Calls.args(D1.inert.node(kids)), accs, lets, path, [])),
      Concat.cwalk(D1.inert.node(kids), conts, accs, lets, path), Concat.cwalk(D1.inert.node(r2), conts, accs, lets,
        path)])
    == List.concat(&2, F.Finding, [Lazy.stop(List<&2, F.Finding>, Bool.not(Bool.and(String.eq(o, "("),
      List.contains(~String, ~String.eq, conts, t))), [], _u => Concat.hits.cont(Calls.args(kids), accs, lets, path,
        [])), Concat.cwalk(kids, conts, accs, lets, path), Concat.cwalk(r2, conts, accs, lets, path)])
    : List<&2, F.Finding>}

def cont.lg(b, t, o, conts, accs, lets, path, kids, r2, ef, ep, ek, ik, ir):
  +aa = Calls.args(kids)
  +hi = Concat.hits.cont(Calls.args(D1.inert.node(kids)), accs, lets, path, [])
  +eh = Equal.trans(List<&2, F.Finding>, hi, Concat.hits.cont(P.inert.nodes(aa), accs, lets, path, []),
    Concat.hits.cont(aa, accs, lets, path, []), Equal.cong(List<&2, Tree.Node>, List<&2, F.Finding>,
      z => Concat.hits.cont(z, accs, lets, path, []),
      Calls.args(D1.inert.node(kids)), P.inert.nodes(aa), P.inert.args(kids)),
    cont.hits(aa, accs, lets, path, [], P.inert.ok.args.go(kids, Tree.NNil{}, [], ek, {==}, {==})))
  P.inert.cat3(Lazy.stop(List<&2, F.Finding>, Bool.not(Bool.and(String.eq(o, "("), List.contains(~String,
    ~String.eq, conts, D1.inert.keep(b, t)))), [], _u => hi), Lazy.stop(List<&2, F.Finding>, Bool.not(Bool.and(
      String.eq(o, "("), List.contains(~String, ~String.eq, conts, t))), [],
      _u => Concat.hits.cont(aa, accs, lets, path, [])),
    Concat.cwalk(D1.inert.node(kids), conts, accs, lets, path), Concat.cwalk(kids, conts, accs, lets, path),
    Concat.cwalk(D1.inert.node(r2), conts, accs, lets, path), Concat.cwalk(r2, conts, accs, lets, path),
    P.inert.stop(Bool.not(Bool.and(String.eq(o, "("), List.contains(~String, ~String.eq, conts,
      D1.inert.keep(b, t)))), Bool.not(Bool.and(String.eq(o, "("), List.contains(~String, ~String.eq, conts, t))),
      hi, Concat.hits.cont(aa, accs, lets, path, []),
      Equal.cong(Bool, Bool, z => Bool.not(Bool.and(String.eq(o, "("), z)),
        List.contains(~String, ~String.eq, conts, D1.inert.keep(b, t)), List.contains(~String, ~String.eq, conts, t),
        cont.mem(conts, b, t, ef, ep)), eh),
    ik, ir)

# the continuation walk reads no string: a leaf's text is compared with the
# continuations, which are plain, and an argument's appends only with names
law cont.walk:
  for nn: Tree.Node
  for +conts: List<&2, String>
  for +accs: List<&2, String>
  for +lets: List<&2, Concat.Let>
  for +path: String
  for +ep: {cont.plain(conts) == True{} : Bool}
  for +e: {D1.inert.ok(nn) == True{} : Bool}
  {Concat.cwalk(D1.inert.node(nn), conts, accs, lets, path) == Concat.cwalk(nn, conts, accs, lets, path)
    : List<&2, F.Finding>}

def cont.walk(nn, conts, accs, lets, path, ep, e):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{+k, +t, +l, +c}:
              match rest:
                case Tree.NCons{h2, +r2}:
                  match h2:
                    case Tree.Group{o, +kids, +cl}:
                      match o:
                        case Lex.Tok{+ok, +ot, +ol, +oc}:
                          +lf = {Tree.Leaf{Lex.Tok{k, t, l, c}} : Tree.Node}
                          +gp = {Tree.Group{Lex.Tok{ok, ot, ol, oc}, kids, cl} : Tree.Node}
                          +eg = P.inert.ok_t(lf, Tree.NCons{gp, r2}, e)
                          +ec = P.inert.ok_h(gp, r2, eg)
                          cont.lg(D1.inert.blanks(k), t, ot, conts, accs, lets, path, kids, r2,
                            P.inert.ok_h(lf, Tree.NCons{gp, r2}, e), ep, ec,
                            cont.walk(kids, conts, accs, lets, path, ep, ec),
                            cont.walk(r2, conts, accs, lets, path, ep, P.inert.ok_t(gp, r2, eg)))
                    case Tree.Leaf{x}:
                      cont.walk(rest, conts, accs, lets, path, ep,
                        P.inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e))
                    case Tree.Stmt{x, y, z}:
                      cont.walk(rest, conts, accs, lets, path, ep,
                        P.inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e))
                    case Tree.NNil{}:
                      cont.walk(rest, conts, accs, lets, path, ep,
                        P.inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e))
                    case Tree.NCons{x, y}:
                      cont.walk(rest, conts, accs, lets, path, ep,
                        P.inert.ok_t(Tree.Leaf{Lex.Tok{k, t, l, c}}, rest, e))
                case Tree.Leaf{x}: {==}
                case Tree.Group{x, y, z}: {==}
                case Tree.Stmt{x, y, z}: {==}
                case Tree.NNil{}: {==}
        case Tree.Group{+o, +kids, +cl}:
          P.inert.cat2(Concat.cwalk(D1.inert.node(kids), conts, accs, lets, path),
            Concat.cwalk(kids, conts, accs, lets, path),
            Concat.cwalk(D1.inert.node(rest), conts, accs, lets, path), Concat.cwalk(rest, conts, accs, lets, path),
            cont.walk(kids, conts, accs, lets, path, ep, P.inert.ok_h(Tree.Group{o, kids, cl}, rest, e)),
            cont.walk(rest, conts, accs, lets, path, ep, P.inert.ok_t(Tree.Group{o, kids, cl}, rest, e)))
        case Tree.Stmt{+sk, +kids, +body}:
          +es = P.inert.ok_h(Tree.Stmt{sk, kids, body}, rest, e)
          +ek = M1.inert.and_l(D1.inert.ok(kids), D1.inert.ok(body), es)
          +la = Concat.after(sk, kids, lets)
          +li = Concat.after(sk, D1.inert.node(kids), lets)
          P.inert.cat3(Concat.cwalk(D1.inert.node(kids), conts, accs, lets, path),
            Concat.cwalk(kids, conts, accs, lets, path), Concat.cwalk(D1.inert.node(body), conts, accs, lets, path),
            Concat.cwalk(body, conts, accs, lets, path), Concat.cwalk(D1.inert.node(rest), conts, accs, li, path),
            Concat.cwalk(rest, conts, accs, la, path),
            cont.walk(kids, conts, accs, lets, path, ep, ek),
            cont.walk(body, conts, accs, lets, path, ep, M1.inert.and_r(D1.inert.ok(kids), D1.inert.ok(body), es)),
            Equal.trans(List<&2, F.Finding>, Concat.cwalk(D1.inert.node(rest), conts, accs, li, path),
              Concat.cwalk(D1.inert.node(rest), conts, accs, la, path), Concat.cwalk(rest, conts, accs, la, path),
              Equal.cong(List<&2, Concat.Let>, List<&2, F.Finding>, z => Concat.cwalk(D1.inert.node(rest), conts,
                accs, z, path), li, la, P.inert.concat.after(sk, kids, lets, ek)),
              cont.walk(rest, conts, accs, la, path, ep, P.inert.ok_t(Tree.Stmt{sk, kids, body}, rest, e))))
        case Tree.NNil{}: cont.walk(rest, conts, accs, lets, path, ep, e)
        case Tree.NCons{x, y}:
          cont.walk(rest, conts, accs, lets, path, ep, P.inert.ok_t(Tree.NCons{x, y}, rest, e))
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

# the signature of the first def as the lexer makes it fits
law cont.dok.sig:
  for +name: String
  for +sig: Tree.Node
  for +body: Tree.Node
  for +rest: List<&2, Calls.Def>
  for +e: {P.inert.dok(Calls.Def{name, sig, body} <> rest) == True{} : Bool}
  {D1.inert.ok(sig) == True{} : Bool}

def cont.dok.sig(name, sig, body, rest, e):
  M1.inert.and_l(D1.inert.ok(sig), D1.inert.ok(body), M1.inert.and_r(Bool.not(D1.inert.marked(name)),
    Bool.and(D1.inert.ok(sig), D1.inert.ok(body)), M1.inert.and_l(Bool.and(Bool.not(D1.inert.marked(name)),
      Bool.and(D1.inert.ok(sig), D1.inert.ok(body))), P.inert.dok(rest), e)))

# one def's walk, its signature and body read that way
law cont.one:
  for +sig: Tree.Node
  for +body: Tree.Node
  for +path: String
  for +es: {D1.inert.ok(sig) == True{} : Bool}
  for +eb: {D1.inert.ok(body) == True{} : Bool}
  {Concat.cwalk(D1.inert.node(body), Concat.conts(D1.inert.node(sig)), Concat.accs(D1.inert.node(sig),
    D1.inert.node(body)), [], path) == Concat.cwalk(body, Concat.conts(sig), Concat.accs(sig, body), [], path)
    : List<&2, F.Finding>}

def cont.one(sig, body, path, es, eb):
  +ib = D1.inert.node(body)
  +isg = D1.inert.node(sig)
  +lhs = Concat.cwalk(ib, Concat.conts(isg), Concat.accs(isg, ib), [], path)
  %cont.walk(body, Concat.conts(sig), Concat.accs(sig, body), [], path, cont.plain.conts(sig, es), eb) :
    {lhs == _ : List<&2, F.Finding>}
  %cont.conts(sig) : {lhs == Concat.cwalk(ib, _, Concat.accs(sig, body), [], path) : List<&2, F.Finding>}
  %cont.accs(sig, body) : {lhs == Concat.cwalk(ib, Concat.conts(isg), _, [], path) : List<&2, F.Finding>}
  {==}

# the continuation half over the defs read that way reports what it reports
# over the defs
law cont.go:
  for ds: List<&2, Calls.Def>
  for +path: String
  for +acc: List<&2, List<&2, F.Finding>>
  for +e: {P.inert.dok(ds) == True{} : Bool}
  {Concat.cont.go(P.inert.defs(ds), path, acc) == Concat.cont.go(ds, path, acc) : List<&2, F.Finding>}

def cont.go(ds, path, acc, e):
  match ds:
    case Nil{}: {==}
    case Con{Calls.Def{+name, +sig, +body}, +rest}:
      +ib = D1.inert.node(body)
      +isg = D1.inert.node(sig)
      +lst = Lazy.stop(List<&2, F.Finding>, Calls.exempt(path, isg), [],
        _u => Concat.cwalk(ib, Concat.conts(isg), Concat.accs(isg, ib), [], path))
      %P.inert.stop(Calls.exempt(path, isg), Calls.exempt(path, sig),
        Concat.cwalk(ib, Concat.conts(isg), Concat.accs(isg, ib), [], path),
        Concat.cwalk(body, Concat.conts(sig), Concat.accs(sig, body), [], path), P.inert.exempt(path, sig),
        cont.one(sig, body, path, cont.dok.sig(name, sig, body, rest, e), P.inert.dok.body(name, sig, body, rest, e))) :
        {Concat.cont.go(P.inert.defs(rest), path, lst <> acc) == Concat.cont.go(rest, path, _ <> acc)
          : List<&2, F.Finding>}
      cont.go(rest, path, lst <> acc, P.inert.dok.rest(name, sig, body, rest, e))

def Laws.inert_concat_cont(
  path,
  _text,
  tree,
  _toks,
  _bound,
  _items,
  _text2,
  tree2,
  _toks2,
  _bound2,
  _items2,
  ok,
  ok2,
  e
):
  M1.inert.via(Tree.Node, z => Concat.cont.go(Calls.defs(z), path, []), tree, tree2, D1.inert.node(tree),
    D1.inert.node(tree2),
    P.inert.lift(z => Concat.cont.go(z, path, []), tree, cont.go(Calls.defs(tree), path, [],
      P.inert.dok.of(tree, ok))),
    P.inert.lift(z => Concat.cont.go(z, path, []), tree2, cont.go(Calls.defs(tree2), path, [],
      P.inert.dok.of(tree2, ok2))),
    e)
