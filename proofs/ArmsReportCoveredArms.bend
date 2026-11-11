# proofs of laws/ArmsReportCoveredArms.bend
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/rules/tokens.bend as T
import ../src/lazy/lazy.bend as Lazy
import ../src/syntax/tree.bend as Tree
import ../src/rules/correctness/arms.bend as Arms
import ../laws/ArmsReportCoveredArms.bend as Laws
import ./lemmas/Pick.bend as M1
import ./lemmas/UnsafeStringCompare.bend as M2

# the count
# ---------

# a covered arm's finding in front adds one to the count
law cover.hit:
  for mm: Maybe<&2, U32>
  for +path: String
  for ll: U32
  for cc: U32
  for -more: List<&2, F.Finding>
  for -m: Nat
  for ih: {List.length(&2, F.Finding, more) == m : Nat}
  {List.length(&2, F.Finding, Arms.cover.hit(mm, path, ll, cc, more))
    == Bool.pick(Nat, Maybe.is_some(&2, U32, mm), 1n+m, m) : Nat}

def cover.hit(mm, _path, _ll, _cc, more, m, ih):
  match mm:
    case None{}:
      ih
    case Some{line}:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, F.Finding, more), m, ih)

# the carried search answers a line exactly when it carried a hit or some
# arm left covers
law cover.above:
  for seen: List<&2, Arms.Seen>
  for +ps: List<&2, Arms.Part>
  for hit: Bool
  for +at: U32
  {Maybe.is_some(&2, U32, Arms.above(seen, ps, hit, at)) == Bool.or(hit, Laws.cover.some(seen, ps)) : Bool}

def cover.above(seen, ps, hit, _at):
  match seen:
    case Nil{}:
      match hit:
        case True{}:
          {==}
        case False{}:
          {==}
    case Con{Arms.Seen{+line, +parts}, +rest}:
      match hit:
        case True{}:
          {==}
        case False{}:
          cover.above(rest, ps, Arms.covers(parts, Some{ps}), line)

# the search, unless the Nat check reports the arm
law cover.find:
  for skip: Bool
  for +seen: List<&2, Arms.Seen>
  for +ps: List<&2, Arms.Part>
  {Maybe.is_some(&2, U32, Arms.cover.find(skip, seen, ps)) == Bool.and(Bool.not(skip), Laws.cover.some(seen, ps))
    : Bool}

def cover.find(skip, seen, ps):
  match skip:
    case True{}:
      {==}
    case False{}:
      cover.above(seen, ps, False{}, 0)

# one case arm onto the arms after it, which hold the law
law cover.case:
  for +pat: Tree.Node
  for +rest: Tree.Node
  for +seen: List<&2, Arms.Seen>
  for +wide: Maybe<&2, Arms.Wide>
  for +nat: Bool
  for +path: String
  for ih: {List.length(&2, F.Finding, Arms.cover.arms(rest, Arms.Seen{Tree.line(pat), Arms.read(pat)} <> seen,
    Arms.widen(wide, Arms.arm(pat)), nat, path))
    == Laws.cover.arms(rest, Arms.Seen{Tree.line(pat), Arms.read(pat)} <> seen,
      Arms.widen(wide, Arms.arm(pat)), nat) : Nat}
  {List.length(&2, F.Finding, Arms.cover.hit(Arms.cover.find(Bool.and(nat, Arms.told(wide, Arms.arm(pat))), seen,
      Arms.read(pat)), path, Tree.line(pat), Tree.col(pat),
      Arms.cover.arms(rest, Arms.Seen{Tree.line(pat), Arms.read(pat)} <> seen,
        Arms.widen(wide, Arms.arm(pat)), nat, path)))
    == Bool.pick(Nat, Bool.and(Bool.not(Bool.and(nat, Arms.told(wide, Arms.arm(pat)))),
        Laws.cover.some(seen, Arms.read(pat))),
      1n+Laws.cover.arms(rest, Arms.Seen{Tree.line(pat), Arms.read(pat)} <> seen,
        Arms.widen(wide, Arms.arm(pat)), nat),
      Laws.cover.arms(rest, Arms.Seen{Tree.line(pat), Arms.read(pat)} <> seen,
        Arms.widen(wide, Arms.arm(pat)), nat)) : Nat}

def cover.case(pat, rest, seen, wide, nat, path, ih):
  Equal.trans(Nat,
    List.length(&2, F.Finding, Arms.cover.hit(Arms.cover.find(Bool.and(nat, Arms.told(wide, Arms.arm(pat))), seen,
      Arms.read(pat)), path, Tree.line(pat), Tree.col(pat),
      Arms.cover.arms(rest, Arms.Seen{Tree.line(pat), Arms.read(pat)} <> seen,
        Arms.widen(wide, Arms.arm(pat)), nat, path))),
    Bool.pick(Nat, Maybe.is_some(&2, U32, Arms.cover.find(Bool.and(nat, Arms.told(wide, Arms.arm(pat))), seen,
        Arms.read(pat))),
      1n+Laws.cover.arms(rest, Arms.Seen{Tree.line(pat), Arms.read(pat)} <> seen,
        Arms.widen(wide, Arms.arm(pat)), nat),
      Laws.cover.arms(rest, Arms.Seen{Tree.line(pat), Arms.read(pat)} <> seen,
        Arms.widen(wide, Arms.arm(pat)), nat)),
    Bool.pick(Nat, Bool.and(Bool.not(Bool.and(nat, Arms.told(wide, Arms.arm(pat)))),
        Laws.cover.some(seen, Arms.read(pat))),
      1n+Laws.cover.arms(rest, Arms.Seen{Tree.line(pat), Arms.read(pat)} <> seen,
        Arms.widen(wide, Arms.arm(pat)), nat),
      Laws.cover.arms(rest, Arms.Seen{Tree.line(pat), Arms.read(pat)} <> seen,
        Arms.widen(wide, Arms.arm(pat)), nat)),
    cover.hit(Arms.cover.find(Bool.and(nat, Arms.told(wide, Arms.arm(pat))), seen, Arms.read(pat)), path,
      Tree.line(pat), Tree.col(pat),
      Arms.cover.arms(rest, Arms.Seen{Tree.line(pat), Arms.read(pat)} <> seen,
        Arms.widen(wide, Arms.arm(pat)), nat, path),
      Laws.cover.arms(rest, Arms.Seen{Tree.line(pat), Arms.read(pat)} <> seen,
        Arms.widen(wide, Arms.arm(pat)), nat),
      ih),
    Equal.cong(Bool, Nat,
      z => Bool.pick(Nat, z,
        1n+Laws.cover.arms(rest, Arms.Seen{Tree.line(pat), Arms.read(pat)} <> seen,
          Arms.widen(wide, Arms.arm(pat)), nat),
        Laws.cover.arms(rest, Arms.Seen{Tree.line(pat), Arms.read(pat)} <> seen,
          Arms.widen(wide, Arms.arm(pat)), nat)),
      Maybe.is_some(&2, U32, Arms.cover.find(Bool.and(nat, Arms.told(wide, Arms.arm(pat))), seen,
        Arms.read(pat))),
      Bool.and(Bool.not(Bool.and(nat, Arms.told(wide, Arms.arm(pat)))), Laws.cover.some(seen, Arms.read(pat))),
      cover.find(Bool.and(nat, Arms.told(wide, Arms.arm(pat))), seen, Arms.read(pat))))

# a match's arms, each against the arms above it
law cover.go:
  for body: Tree.Node
  for +seen: List<&2, Arms.Seen>
  for +wide: Maybe<&2, Arms.Wide>
  for +nat: Bool
  for +path: String
  {List.length(&2, F.Finding, Arms.cover.arms(body, seen, wide, nat, path)) == Laws.cover.arms(body, seen, wide, nat)
    : Nat}

def cover.go(body, seen, wide, nat, path):
  match body:
    case Tree.Leaf{Lex.Tok{+k1, +x1, +l1, +c1}}:
      {==}
    case Tree.Group{+op1, +ks1, +cl1}:
      {==}
    case Tree.Stmt{+sk1, +sks1, +sb1}:
      {==}
    case Tree.NNil{}:
      {==}
    case Tree.NCons{+h1, +t1}:
      match h1:
        case Tree.Leaf{Lex.Tok{+k2, +x2, +l2, +c2}}:
          cover.go(t1, seen, wide, nat, path)
        case Tree.Group{+op2, +ks2, +cl2}:
          cover.go(t1, seen, wide, nat, path)
        case Tree.Stmt{+sk2, +sks2, +sb2}:
          match sk2:
            case Tree.SDef{}:
              cover.go(t1, seen, wide, nat, path)
            case Tree.SType{}:
              cover.go(t1, seen, wide, nat, path)
            case Tree.SLaw{}:
              cover.go(t1, seen, wide, nat, path)
            case Tree.SImport{}:
              cover.go(t1, seen, wide, nat, path)
            case Tree.SCase{}:
              cover.case(T.pattern(sks2), t1, seen, wide, nat, path,
                cover.go(t1, Arms.Seen{Tree.line(T.pattern(sks2)), Arms.read(T.pattern(sks2))} <> seen,
                  Arms.widen(wide, Arms.arm(T.pattern(sks2))), nat, path))
            case Tree.SFor{}:
              cover.go(t1, seen, wide, nat, path)
            case Tree.SLet{}:
              cover.go(t1, seen, wide, nat, path)
            case Tree.STerm{}:
              cover.go(t1, seen, wide, nat, path)
        case Tree.NNil{}:
          cover.go(t1, seen, wide, nat, path)
        case Tree.NCons{+h2, +t2}:
          cover.go(t1, seen, wide, nat, path)

# one statement onto the rest, its body and the rest both holding the law
law cover.stmt:
  for +kids: Tree.Node
  for +body: Tree.Node
  for +rest: Tree.Node
  for +path: String
  for ihb: {List.length(&2, F.Finding, Arms.cover.walk(body, path)) == Laws.cover_count(body) : Nat}
  for ihr: {List.length(&2, F.Finding, Arms.cover.walk(rest, path)) == Laws.cover_count(rest) : Nat}
  {List.length(&2, F.Finding, List.concat(&2, F.Finding, [Lazy.stop(List<&2, F.Finding>,
      Bool.not(T.keyword(kids, "match")), [], _u => Arms.cover.arms(body, [], None{}, Arms.single(kids), path)),
      Arms.cover.walk(body, path), Arms.cover.walk(rest, path)]))
    == Nat.add(Bool.pick(Nat, T.keyword(kids, "match"), Laws.cover.arms(body, [], None{}, Arms.single(kids)), 0n),
      Nat.add(Laws.cover_count(body), Laws.cover_count(rest))) : Nat}

def cover.stmt(kids, body, rest, path, ihb, ihr):
  Equal.trans(Nat,
    List.length(&2, F.Finding, List.concat(&2, F.Finding, [Lazy.stop(List<&2, F.Finding>,
      Bool.not(T.keyword(kids, "match")), [], _u => Arms.cover.arms(body, [], None{}, Arms.single(kids), path)),
      Arms.cover.walk(body, path), Arms.cover.walk(rest, path)])),
    Nat.add(List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, Bool.not(T.keyword(kids, "match")), [],
      _u => Arms.cover.arms(body, [], None{}, Arms.single(kids), path))),
      Nat.add(List.length(&2, F.Finding, Arms.cover.walk(body, path)),
        List.length(&2, F.Finding, Arms.cover.walk(rest, path)))),
    Nat.add(Bool.pick(Nat, T.keyword(kids, "match"), Laws.cover.arms(body, [], None{}, Arms.single(kids)), 0n),
      Nat.add(Laws.cover_count(body), Laws.cover_count(rest))),
    M1.arms.cat(Lazy.stop(List<&2, F.Finding>, Bool.not(T.keyword(kids, "match")), [],
      _u => Arms.cover.arms(body, [], None{}, Arms.single(kids), path)),
      Arms.cover.walk(body, path), Arms.cover.walk(rest, path)),
    M1.arms.add3(List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, Bool.not(T.keyword(kids, "match")), [],
      _u => Arms.cover.arms(body, [], None{}, Arms.single(kids), path))),
      Bool.pick(Nat, T.keyword(kids, "match"), Laws.cover.arms(body, [], None{}, Arms.single(kids)), 0n),
      List.length(&2, F.Finding, Arms.cover.walk(body, path)), Laws.cover_count(body),
      List.length(&2, F.Finding, Arms.cover.walk(rest, path)), Laws.cover_count(rest),
      Equal.trans(Nat,
        List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, Bool.not(T.keyword(kids, "match")), [],
          _u => Arms.cover.arms(body, [], None{}, Arms.single(kids), path))),
        Bool.pick(Nat, Bool.not(T.keyword(kids, "match")), 0n,
          Laws.cover.arms(body, [], None{}, Arms.single(kids))),
        Bool.pick(Nat, T.keyword(kids, "match"), Laws.cover.arms(body, [], None{}, Arms.single(kids)), 0n),
        M1.param.stop(Bool.not(T.keyword(kids, "match")),
          Arms.cover.arms(body, [], None{}, Arms.single(kids), path),
          Laws.cover.arms(body, [], None{}, Arms.single(kids)),
          cover.go(body, [], None{}, Arms.single(kids), path)),
        M1.arms.flip(T.keyword(kids, "match"), Laws.cover.arms(body, [], None{}, Arms.single(kids)))),
      ihb, ihr))

# every statement at any depth, each match's arms read
law cover.walk:
  for nn: Tree.Node
  for +path: String
  {List.length(&2, F.Finding, Arms.cover.walk(nn, path)) == Laws.cover_count(nn) : Nat}

def cover.walk(nn, path):
  match nn:
    case Tree.Leaf{Lex.Tok{+k1, +x1, +l1, +c1}}:
      {==}
    case Tree.Group{+op1, +ks1, +cl1}:
      {==}
    case Tree.Stmt{+sk1, +sks1, +sb1}:
      {==}
    case Tree.NNil{}:
      {==}
    case Tree.NCons{+h1, +t1}:
      match h1:
        case Tree.Leaf{Lex.Tok{+k2, +x2, +l2, +c2}}:
          cover.walk(t1, path)
        case Tree.Group{+op2, +ks2, +cl2}:
          cover.walk(t1, path)
        case Tree.Stmt{+sk2, +sks2, +sb2}:
          cover.stmt(sks2, sb2, t1, path, cover.walk(sb2, path), cover.walk(t1, path))
        case Tree.NNil{}:
          cover.walk(t1, path)
        case Tree.NCons{+h2, +t2}:
          cover.walk(t1, path)

def Laws.arms_cover_counts(path, _text, _toks, tree, _bound, _items):
  cover.walk(Arms.blank(tree), path)

# what covers answers
# -------------------

# a pattern with nothing left to read against covers nothing
law cover.none:
  for ps: List<&2, Arms.Part>
  {Arms.covers(ps, None{}) == False{} : Bool}

def cover.none(ps):
  match ps:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

# a lone word against a lone word covers exactly when the test of their
# texts says so
law cover.word:
  for bb: Bool
  {Arms.covers(Nil{}, Bool.pick(Maybe<&2, List<&2, Arms.Part>>, bb, Some{Nil{}}, None{})) == bb : Bool}

def cover.word(bb):
  match bb:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.arms_cover_word(tt, uu):
  cover.word(String.eq(tt, uu))

def Laws.arms_cover_same_word(tt):
  Equal.trans(Bool, Arms.covers([Arms.PWord{tt}], Some{[Arms.PWord{tt}]}), String.eq(tt, tt), True{},
    cover.word(String.eq(tt, tt)), M2.unsafe.srefl(tt))

def Laws.arms_cover_binder_word(_tt):
  {==}

def Laws.arms_cover_binder_ctor(_tt, _open, _close):
  {==}

def Laws.arms_cover_binder_nested(_tt, _uu, _open, _close):
  {==}

def Laws.arms_cover_binder_string(_tt):
  {==}

def Laws.arms_cover_binder_plus(_tt):
  {==}

def Laws.arms_cover_word_not_binder(_tt):
  {==}

def Laws.arms_cover_same_shape(tt, open, close):
  %Equal.sym(Bool, String.eq(tt, tt), True{}, M2.unsafe.srefl(tt)) :
    {Arms.covers([Arms.POpen{open}, Arms.PAny{}, Arms.PComma{}, Arms.PAny{}, Arms.PClose{close}],
      Bool.pick(Maybe<&2, List<&2, Arms.Part>>, _,
        Some{[Arms.POpen{open}, Arms.PAny{}, Arms.PComma{}, Arms.PAny{}, Arms.PClose{close}]}, None{}))
      == True{} : Bool}
  %Equal.sym(Bool, String.eq(open, open), True{}, M2.unsafe.srefl(open)) :
    {Arms.covers([Arms.PAny{}, Arms.PComma{}, Arms.PAny{}, Arms.PClose{close}],
      Bool.pick(Maybe<&2, List<&2, Arms.Part>>, _,
        Some{[Arms.PAny{}, Arms.PComma{}, Arms.PAny{}, Arms.PClose{close}]}, None{}))
      == True{} : Bool}
  %Equal.sym(Bool, String.eq(close, close), True{}, M2.unsafe.srefl(close)) :
    {Arms.covers(Nil{}, Bool.pick(Maybe<&2, List<&2, Arms.Part>>, _, Some{Nil{}}, None{})) == True{} : Bool}
  {==}

def Laws.arms_cover_head_tail(_tt, _uu, _vv):
  {==}

def Laws.arms_cover_binder_list(_tt, _open, _close):
  {==}

def Laws.arms_cover_longer_not(_tt):
  {==}

def Laws.arms_cover_string_never(ps, _qs):
  cover.none(ps)

def Laws.arms_cover_unread_never(ps, _qs):
  cover.none(ps)

def Laws.arms_cover_unread_not(ps):
  match ps:
    case Nil{}:
      {==}
    case Con{h, t}:
      match h:
        case Arms.PAny{}:
          cover.none(t)
        case Arms.PWord{x}:
          cover.none(t)
        case Arms.PPlus{x}:
          cover.none(t)
        case Arms.PStr{}:
          cover.none(t)
        case Arms.POpen{x}:
          cover.none(t)
        case Arms.PClose{x}:
          cover.none(t)
        case Arms.PComma{}:
          cover.none(t)
        case Arms.PCons{}:
          cover.none(t)
        case Arms.PBad{}:
          cover.none(t)

# what parts reads
# ----------------

def Laws.arms_reads_name(_tt, _ll, _cc):
  {==}

def Laws.arms_reads_ctor(_tt, _ll, _cc):
  {==}

def Laws.arms_reads_mark(_tt, _ll, _cc):
  {==}

def Laws.arms_reads_plus(_kk, _tt, _ll, _cc):
  {==}

def Laws.arms_reads_to_colon(_tt, _uu, _ll, _cc, _rest):
  {==}

def Laws.arms_reads_string(_tt, _ll, _cc):
  {==}

def Laws.arms_reads_wrapped(pat, e):
  %Equal.sym(Bool, Arms.ended(pat), False{}, e) :
    {Arms.read.on(_, pat) == [Arms.PBad{}] : List<&2, Arms.Part>}
  {==}

def Laws.arms_reads_ended(pat, e):
  %Equal.sym(Bool, Arms.ended(pat), True{}, e) :
    {Arms.read.on(_, pat) == Arms.parts(Tree.leaves(Arms.cut(pat))) : List<&2, Arms.Part>}
  {==}
