# proofs of laws/UnusedReportsDeadBinders.bend
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/syntax/bind.bend as Bind
import ../src/lazy/lazy.bend as Lazy
import ../src/syntax/tree.bend as Tree
import ../src/rules/suspicious/unused.bend as Unused
import ../laws/UnusedReportsDeadBinders.bend as Laws
import ./lemmas/Nat.bend as M1
import ./lemmas/UnusedBinderPick.bend as M2
import ./lemmas/UnusedEarlyOr.bend as M3

# The binding rule, unused: the rule's foreign lines are the law's header
# lines, its kind test and use search are the law's, and each binder adds the
# finding the law counts.

# the lines of some tokens onto acc are those lines, then acc
law unused.lines:
  for ts: List<&2, Lex.Tok>
  for +acc: List<&2, U32>
  {Unused.lines(ts, acc) == List.append(&2, U32, Laws.unused.token_lines(ts), acc) : List<&2, U32>}

def unused.lines(ts, acc):
  match ts:
    case Nil{}:
      {==}
    case Con{Lex.Tok{k, t, +l, c}, rest}:
      Equal.cong(List<&2, U32>, List<&2, U32>, xs => l <> xs, Unused.lines(rest, acc),
        List.append(&2, U32, Laws.unused.token_lines(rest), acc), unused.lines(rest, acc))

# a foreign def's header lines onto the lines after it, to the rule and to
# the law
law unused.header:
  for +kids: Tree.Node
  for +rest: Tree.Node
  for ih: {Unused.foreign(rest) == Laws.unused.headers(rest) : List<&2, U32>}
  {Unused.lines(Tree.leaves(kids), Unused.foreign(rest))
    == List.append(&2, U32, Laws.unused.token_lines(Tree.leaves(kids)), Laws.unused.headers(rest)) : List<&2, U32>}

def unused.header(kids, rest, ih):
  Equal.trans(List<&2, U32>,
    Unused.lines(Tree.leaves(kids), Unused.foreign(rest)),
    List.append(&2, U32, Laws.unused.token_lines(Tree.leaves(kids)), Unused.foreign(rest)),
    List.append(&2, U32, Laws.unused.token_lines(Tree.leaves(kids)), Laws.unused.headers(rest)),
    unused.lines(Tree.leaves(kids), Unused.foreign(rest)),
    Equal.cong(List<&2, U32>, List<&2, U32>, xs => List.append(&2, U32, Laws.unused.token_lines(Tree.leaves(kids)), xs),
      Unused.foreign(rest), Laws.unused.headers(rest), ih))

# the rule's `:` test on a statement's chain is the law's
law unused.ends:
  for kids: Tree.Node
  for last: Bool
  {Unused.foreign.ends(kids, last) == Laws.unused.ends(kids, last) : Bool}

def unused.ends(kids, _last):
  match kids:
    case Tree.NCons{h, t}:
      unused.ends(t, Unused.colon(h))
    case Tree.Leaf{x}:
      {==}
    case Tree.Group{x, y, z}:
      {==}
    case Tree.Stmt{x, y, z}:
      {==}
    case Tree.NNil{}:
      {==}

# the rule's import test is the law's
law unused.first:
  for sk: Tree.StmtKind
  {Unused.foreign.first(sk) == Laws.unused.is_import(sk) : Bool}

def unused.first(sk):
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
      {==}
    case Tree.STerm{}:
      {==}

# the rule's test for a body that opens with an import once the header is
# over is the law's, whether the header is still open or not
law unused.opens:
  for body: Tree.Node
  for open: Bool
  {Unused.foreign.opens(body, open) == Laws.unused.opens(body, open) : Bool}

def unused.opens(body, open):
  match body:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Stmt{sk, +kids, b}:
          match open:
            case True{}:
              Equal.trans(Bool, Unused.foreign.opens(rest, Bool.not(Unused.foreign.ends(kids, False{}))),
                Laws.unused.opens(rest, Bool.not(Unused.foreign.ends(kids, False{}))),
                Laws.unused.opens(rest, Bool.not(Laws.unused.ends(kids, False{}))),
                unused.opens(rest, Bool.not(Unused.foreign.ends(kids, False{}))),
                Equal.cong(Bool, Bool, z => Laws.unused.opens(rest, Bool.not(z)), Unused.foreign.ends(kids, False{}),
                  Laws.unused.ends(kids, False{}), unused.ends(kids, False{})))
            case False{}:
              unused.first(sk)
        case Tree.Leaf{x}:
          {==}
        case Tree.Group{x, y, z}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{x, y}:
          {==}
    case Tree.Leaf{x}:
      {==}
    case Tree.Group{x, y, z}:
      {==}
    case Tree.Stmt{x, y, z}:
      {==}
    case Tree.NNil{}:
      {==}

# a def's lines onto the lines after it, to the rule and to the law
law unused.def:
  for +kids: Tree.Node
  for +body: Tree.Node
  for +rest: Tree.Node
  for +ih: {Unused.foreign(rest) == Laws.unused.headers(rest) : List<&2, U32>}
  {Bool.pick(List<&2, U32>, Unused.foreign.opens(body, Bool.not(Unused.foreign.ends(kids, False{}))),
    Unused.lines(Tree.leaves(kids), Unused.foreign(rest)), Unused.foreign(rest))
    == Bool.pick(List<&2, U32>, Laws.unused.imported(kids, body),
      List.append(&2, U32, Laws.unused.token_lines(Tree.leaves(kids)), Laws.unused.headers(rest)),
      Laws.unused.headers(rest)) : List<&2, U32>}

def unused.def(kids, body, rest, ih):
  +rc = Unused.foreign.opens(body, Bool.not(Unused.foreign.ends(kids, False{})))
  +lc = Laws.unused.imported(kids, body)
  +ra = Unused.lines(Tree.leaves(kids), Unused.foreign(rest))
  +la = List.append(&2, U32, Laws.unused.token_lines(Tree.leaves(kids)), Laws.unused.headers(rest))
  +ec = Equal.trans(Bool, rc, Laws.unused.opens(body, Bool.not(Unused.foreign.ends(kids, False{}))), lc,
    unused.opens(body, Bool.not(Unused.foreign.ends(kids, False{}))),
    Equal.cong(Bool, Bool, z => Laws.unused.opens(body, Bool.not(z)), Unused.foreign.ends(kids, False{}),
      Laws.unused.ends(kids, False{}), unused.ends(kids, False{})))
  Equal.trans(List<&2, U32>, Bool.pick(List<&2, U32>, rc, ra, Unused.foreign(rest)),
    Bool.pick(List<&2, U32>, lc, ra, Unused.foreign(rest)),
    Bool.pick(List<&2, U32>, lc, la, Laws.unused.headers(rest)),
    Equal.cong(Bool, List<&2, U32>, z => Bool.pick(List<&2, U32>, z, ra, Unused.foreign(rest)), rc, lc, ec),
    M2.unused.pick(lc, ra, la, Unused.foreign(rest), Laws.unused.headers(rest), unused.header(kids, rest, ih), ih))

# the rule's foreign lines are the law's header lines
law unused.foreign:
  for root: Tree.Node
  {Unused.foreign(root) == Laws.unused.headers(root) : List<&2, U32>}

def unused.foreign(root):
  match root:
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
        case Tree.Leaf{tok}:
          unused.foreign(rest)
        case Tree.Group{o, gk, cl}:
          unused.foreign(rest)
        case Tree.Stmt{kind, +kids, +body}:
          match kind:
            case Tree.SDef{}:
              unused.def(kids, body, rest, unused.foreign(rest))
            case Tree.SType{}:
              unused.foreign(rest)
            case Tree.SLaw{}:
              unused.foreign(rest)
            case Tree.SImport{}:
              unused.foreign(rest)
            case Tree.SCase{}:
              unused.foreign(rest)
            case Tree.SFor{}:
              unused.foreign(rest)
            case Tree.SLet{}:
              unused.foreign(rest)
            case Tree.STerm{}:
              unused.foreign(rest)
        case Tree.NNil{}:
          unused.foreign(rest)
        case Tree.NCons{nh, nt}:
          unused.foreign(rest)

# the rule's use search is the law's
law unused.used:
  for uses: List<&2, Bind.Use>
  for +line: U32
  for +col: U32
  {Unused.used(uses, line, col) == Laws.unused.seen(uses, line, col) : Bool}

def unused.used(uses, line, col):
  match uses:
    case Nil{}:
      {==}
    case Con{Bind.Use{n, l, c, tg}, +rest}:
      match tg:
        case Bind.TLocal{+tl, +tc}:
          M3.unused.or(Bool.and(U32.is_eq(tl, line), U32.is_eq(tc, col)), Unused.used(rest, line, col),
            Laws.unused.seen(rest, line, col), unused.used(rest, line, col))
        case Bind.TItem{nm}:
          unused.used(rest, line, col)
        case Bind.TQual{a, nm}:
          unused.used(rest, line, col)
        case Bind.TFree{}:
          unused.used(rest, line, col)

# the rule's kind test is the law's
law unused.kind:
  for kk: Bind.BindKind
  for +note: String
  for +line: U32
  for +fl: List<&2, U32>
  {Unused.reportable(kk, note, line, fl) == Laws.unused.kept(kk, note, line, fl) : Bool}

def unused.kind(kk, _note, _line, _fl):
  match kk:
    case Bind.KItem{}:
      {==}
    case Bind.KCtor{}:
      {==}
    case Bind.KParam{}:
      {==}
    case Bind.KTypeParam{}:
      {==}
    case Bind.KField{}:
      {==}
    case Bind.KLocal{}:
      {==}
    case Bind.KPat{}:
      {==}
    case Bind.KFor{}:
      {==}
    case Bind.KTypeVar{}:
      {==}

# an `or` of a Bool with itself is that Bool
law unused.or_self:
  for a: Bool
  {Bool.or(a, a) == a : Bool}

def unused.or_self(a):
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# a stop at the first True, against the `or` it stops early on, adds nothing
law unused.or_absorb:
  for e: Bool
  for a: Bool
  {Bool.or(Lazy.or_else(e, _u => a), Bool.or(e, a)) == Bool.or(e, a) : Bool}

def unused.or_absorb(e, a):
  match e:
    case True{}:
      {==}
    case False{}:
      unused.or_self(a)

# a hit already on the right adds nothing on the left
law unused.or_again:
  for g: Bool
  for e: Bool
  {Bool.or(g, Bool.or(e, g)) == Bool.or(e, g) : Bool}

def unused.or_again(g, e):
  match g:
    case True{}:
      match e:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      {==}

# nothing is found in the empty index, whatever the path
law unused.none:
  for qq: List<&2, Bool>
  for +line: U32
  for +col: U32
  {Unused.find(qq, Unused.HNone{}, line, col) == False{} : Bool}

def unused.none(qq, line, col):
  match qq:
    case Nil{}:
      {==}
    case Con{b, r}:
      match b:
        case True{}:
          unused.none(r, line, col)
        case False{}:
          unused.none(r, line, col)

# a hit in the index after a cell goes in is that cell, or a hit before it:
# the index is sound, whatever the two paths
law unused.put:
  for pp: List<&2, Bool>
  for +qq: List<&2, Bool>
  for +hh: Unused.Hits
  for +l1: U32
  for +c1: U32
  for +l2: U32
  for +c2: U32
  {Bool.or(Unused.find(qq, Unused.put(pp, hh, Unused.Cell{l1, c1}), l2, c2),
      Bool.or(Bool.and(U32.is_eq(l1, l2), U32.is_eq(c1, c2)), Unused.find(qq, hh, l2, c2)))
    == Bool.or(Bool.and(U32.is_eq(l1, l2), U32.is_eq(c1, c2)), Unused.find(qq, hh, l2, c2)) : Bool}

def unused.put(pp, qq, hh, l1, c1, l2, c2):
  match pp:
    case Nil{}:
      match qq:
        case Nil{}:
          unused.or_absorb(Bool.and(U32.is_eq(l1, l2), U32.is_eq(c1, c2)),
            Unused.hits.any(Unused.hits.cells(hh), l2, c2))
        case Con{b2, r2}:
          match b2:
            case True{}:
              %Equal.sym(Bool, Unused.find(r2, Unused.HNone{}, l2, c2), False{}, unused.none(r2, l2, c2)) :
                {Bool.or(_, Bool.or(Bool.and(U32.is_eq(l1, l2), U32.is_eq(c1, c2)),
                Unused.find(r2, Unused.hits.lo(hh), l2, c2)))
                == Bool.or(Bool.and(U32.is_eq(l1, l2), U32.is_eq(c1, c2)),
                  Unused.find(r2, Unused.hits.lo(hh), l2, c2)) : Bool}
              {==}
            case False{}:
              %Equal.sym(Bool, Unused.find(r2, Unused.HNone{}, l2, c2), False{}, unused.none(r2, l2, c2)) :
                {Bool.or(_, Bool.or(Bool.and(U32.is_eq(l1, l2), U32.is_eq(c1, c2)),
                Unused.find(r2, Unused.hits.hi(hh), l2, c2)))
                == Bool.or(Bool.and(U32.is_eq(l1, l2), U32.is_eq(c1, c2)),
                  Unused.find(r2, Unused.hits.hi(hh), l2, c2)) : Bool}
              {==}
    case Con{b1, r1}:
      match b1:
        case True{}:
          match qq:
            case Nil{}:
              {==}
            case Con{b2, r2}:
              match b2:
                case True{}:
                  unused.put(r1, r2, Unused.hits.lo(hh), l1, c1, l2, c2)
                case False{}:
                  unused.or_again(Unused.find(r2, Unused.hits.hi(hh), l2, c2),
                    Bool.and(U32.is_eq(l1, l2), U32.is_eq(c1, c2)))
        case False{}:
          match qq:
            case Nil{}:
              {==}
            case Con{b2, r2}:
              match b2:
                case True{}:
                  unused.or_again(Unused.find(r2, Unused.hits.lo(hh), l2, c2),
                    Bool.and(U32.is_eq(l1, l2), U32.is_eq(c1, c2)))
                case False{}:
                  unused.put(r1, r2, Unused.hits.hi(hh), l1, c1, l2, c2)

# Unit for True, Empty for False
def unused.true_ty(bb: Bool) -> Type:
  match bb:
    case True{}:
      Unit
    case False{}:
      Empty

# True is never False
law unused.true_false:
  for e: {True{} == False{} : Bool}
  Empty

def unused.true_false(e):
  %e : unused.true_ty(_)
  Unit{}

# one more cell keeps an index sound: a hit after it is the new cell, or a
# hit before it, which the uses already had
law unused.step:
  for e: Bool
  for fp: Bool
  for f: Bool
  for s: Bool
  for h1: {Bool.or(fp, Bool.or(e, f)) == Bool.or(e, f) : Bool}
  for h2: {Bool.or(f, s) == s : Bool}
  {Bool.or(fp, Bool.or(e, s)) == Bool.or(e, s) : Bool}

def unused.step(e, fp, f, s, h1, h2):
  match e:
    case True{}:
      match fp:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      match fp:
        case True{}:
          match f:
            case True{}:
              h2
            case False{}:
              Empty.absurd({True{} == s : Bool}, unused.true_false(h1))
        case False{}:
          {==}

# the index of the uses is sound: anything found in it, down any path, is a
# use's target
law unused.index:
  for uses: List<&2, Bind.Use>
  for +qq: List<&2, Bool>
  for +line: U32
  for +col: U32
  {Bool.or(Unused.find(qq, Unused.index(uses), line, col), Laws.unused.seen(uses, line, col))
    == Laws.unused.seen(uses, line, col) : Bool}

def unused.index(uses, qq, line, col):
  match uses:
    case Nil{}:
      %Equal.sym(Bool, Unused.find(qq, Unused.HNone{}, line, col), False{}, unused.none(qq, line, col)) :
        {Bool.or(_, False{}) == False{} : Bool}
      {==}
    case Con{Bind.Use{n, l, c, tg}, +rest}:
      match tg:
        case Bind.TLocal{+tl, +tc}:
          unused.step(Bool.and(U32.is_eq(tl, line), U32.is_eq(tc, col)),
            Unused.find(qq, Unused.put(Unused.path(Unused.depth(), tl), Unused.index(rest), Unused.Cell{tl, tc}),
              line, col),
            Unused.find(qq, Unused.index(rest), line, col), Laws.unused.seen(rest, line, col),
            unused.put(Unused.path(Unused.depth(), tl), qq, Unused.index(rest), tl, tc, line, col),
            unused.index(rest, qq, line, col))
        case Bind.TItem{nm}:
          unused.index(rest, qq, line, col)
        case Bind.TQual{a, nm}:
          unused.index(rest, qq, line, col)
        case Bind.TFree{}:
          unused.index(rest, qq, line, col)

# a sound hit, else the scan, is the scan
law unused.fast:
  for f: Bool
  for -u: Bool
  for -s: Bool
  for hu: {u == s : Bool}
  for hs: {Bool.or(f, s) == s : Bool}
  {Lazy.or_else(f, _u => u) == s : Bool}

def unused.fast(f, _u, _s, hu, hs):
  match f:
    case True{}:
      hs
    case False{}:
      hu

# the rule's use search, through the index of the uses, is the law's
law unused.seen:
  for +uses: List<&2, Bind.Use>
  for +line: U32
  for +col: U32
  {Unused.seen(Unused.index(uses), uses, line, col) == Laws.unused.seen(uses, line, col) : Bool}

def unused.seen(uses, line, col):
  unused.fast(Unused.find(Unused.path(Unused.depth(), line), Unused.index(uses), line, col),
    Unused.used(uses, line, col), Laws.unused.seen(uses, line, col), unused.used(uses, line, col),
    unused.index(uses, Unused.path(Unused.depth(), line), line, col))

# a stop at the first False is Bool.and
law unused.and:
  for a: Bool
  for -b: Bool
  {Lazy.and_then(a, _u => b) == Bool.and(a, b) : Bool}

def unused.and(a, _b):
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# the rule's finding test for a binder is the law's
law unused.hit:
  for +kk: Bind.BindKind
  for +name: String
  for +note: String
  for +line: U32
  for +col: U32
  for +uses: List<&2, Bind.Use>
  for +fl: List<&2, U32>
  {Lazy.and_then(Bool.and(Unused.reportable(kk, note, line, fl), Bool.not(String.starts_with(name, "_"))),
      _u => Bool.not(Unused.seen(Unused.index(uses), uses, line, col)))
    == Bool.and(Bool.and(Laws.unused.kept(kk, note, line, fl), Bool.not(String.starts_with(name, "_"))),
      Bool.not(Laws.unused.seen(uses, line, col))) : Bool}

def unused.hit(kk, name, note, line, col, uses, fl):
  +sr = Unused.seen(Unused.index(uses), uses, line, col)
  Equal.trans(Bool,
    Lazy.and_then(Bool.and(Unused.reportable(kk, note, line, fl), Bool.not(String.starts_with(name, "_"))),
      _u => Bool.not(sr)),
    Bool.and(Bool.and(Unused.reportable(kk, note, line, fl), Bool.not(String.starts_with(name, "_"))),
      Bool.not(sr)),
    Bool.and(Bool.and(Laws.unused.kept(kk, note, line, fl), Bool.not(String.starts_with(name, "_"))),
      Bool.not(Laws.unused.seen(uses, line, col))),
    unused.and(Bool.and(Unused.reportable(kk, note, line, fl), Bool.not(String.starts_with(name, "_"))),
      Bool.not(sr)),
    Equal.trans(Bool,
      Bool.and(Bool.and(Unused.reportable(kk, note, line, fl), Bool.not(String.starts_with(name, "_"))),
        Bool.not(sr)),
      Bool.and(Bool.and(Laws.unused.kept(kk, note, line, fl), Bool.not(String.starts_with(name, "_"))),
        Bool.not(sr)),
      Bool.and(Bool.and(Laws.unused.kept(kk, note, line, fl), Bool.not(String.starts_with(name, "_"))),
        Bool.not(Laws.unused.seen(uses, line, col))),
      Equal.cong(Bool, Bool,
        z => Bool.and(Bool.and(z, Bool.not(String.starts_with(name, "_"))), Bool.not(sr)),
        Unused.reportable(kk, note, line, fl), Laws.unused.kept(kk, note, line, fl), unused.kind(kk, note, line, fl)),
      Equal.cong(Bool, Bool,
        z => Bool.and(Bool.and(Laws.unused.kept(kk, note, line, fl), Bool.not(String.starts_with(name, "_"))),
          Bool.not(z)),
        sr, Laws.unused.seen(uses, line, col), unused.seen(uses, line, col))))

# over the binder list, the rule counts what the law counts
law unused.go:
  for binds: List<&2, Bind.Bind>
  for +uses: List<&2, Bind.Use>
  for +fl: List<&2, U32>
  for +path: String
  {List.length(&2, F.Finding, Unused.check.go(binds, Unused.index(uses), uses, fl, path))
    == Laws.unused.count(binds, uses, fl) : Nat}

def unused.go(binds, uses, fl, path):
  match binds:
    case Nil{}:
      {==}
    case Con{Bind.Bind{+name, +line, +col, +kk, +note}, +rest}:
      +m = Laws.unused.count(rest, uses, fl)
      +b = Lazy.and_then(Bool.and(Unused.reportable(kk, note, line, fl), Bool.not(String.starts_with(name, "_"))),
        _u => Bool.not(Unused.seen(Unused.index(uses), uses, line, col)))
      Equal.trans(Nat,
        List.length(&2, F.Finding,
          Unused.check.go(Bind.Bind{name, line, col, kk, note} <> rest, Unused.index(uses), uses, fl, path)),
        Bool.pick(Nat, b, 1n+m, m),
        Laws.unused.count(Bind.Bind{name, line, col, kk, note} <> rest, uses, fl),
        M1.nat.pick(b, F.Finding{path, line, col, U32.from_nat(String.length(name)), "unused",
            Unused.what(kk) ++ " " ++ name ++ " is never used."},
          Unused.check.go(rest, Unused.index(uses), uses, fl, path), m, unused.go(rest, uses, fl, path)),
        Equal.cong(Bool, Nat, z => Bool.pick(Nat, z, 1n+m, m), b,
          Bool.and(Bool.and(Laws.unused.kept(kk, note, line, fl), Bool.not(String.starts_with(name, "_"))),
            Bool.not(Laws.unused.seen(uses, line, col))),
          unused.hit(kk, name, note, line, col, uses, fl)))

def Laws.unused_counts(path, _text, _toks, tree, binds, uses, _scopes, _items):
  Equal.trans(Nat,
    List.length(&2, F.Finding, Unused.check.go(binds, Unused.index(uses), uses, Unused.foreign(tree), path)),
    Laws.unused.count(binds, uses, Unused.foreign(tree)),
    Laws.unused.count(binds, uses, Laws.unused.headers(tree)),
    unused.go(binds, uses, Unused.foreign(tree), path),
    Equal.cong(List<&2, U32>, Nat, z => Laws.unused.count(binds, uses, z),
      Unused.foreign(tree), Laws.unused.headers(tree), unused.foreign(tree)))
