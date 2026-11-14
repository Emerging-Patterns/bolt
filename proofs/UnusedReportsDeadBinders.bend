# proofs of laws/UnusedReportsDeadBinders.bend
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/syntax/bind.bend as Bind
import ../src/lazy/lazy.bend as Lazy
import ../src/syntax/tree.bend as Tree
import ../src/rules/suspicious/unused.bend as Unused
import ../src/rules/calls.bend as Calls
import ../laws/UnusedReportsDeadBinders.bend as Laws
import ./lemmas/Nat.bend as M1
import ./lemmas/UnusedBinderPick.bend as M2
import ./lemmas/UnusedEarlyOr.bend as M3
import ./lemmas/BinderIndex.bend as M4
import ./lemmas/InertTextFacts.bend as M5

# The binding rule, unused: the rule's foreign lines are the law's header
# lines, its kind test is the law's, its index of the uses answers as the
# law's search of them does, and each binder adds the finding the law counts.

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

# the rule's test for a body that opens with an import is the law's
law unused.opens:
  for body: Tree.Node
  {Unused.foreign.opens(body) == Laws.unused.opens(body) : Bool}

def unused.opens(body):
  match body:
    case Tree.NCons{h, rest}:
      match h:
        case Tree.Stmt{sk, kids, b}:
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
  {Bool.pick(List<&2, U32>, Unused.foreign.opens(Calls.under(kids, body)),
    Unused.lines(Tree.leaves(kids), Unused.foreign(rest)), Unused.foreign(rest))
    == Bool.pick(List<&2, U32>, Laws.unused.imported(kids, body),
      List.append(&2, U32, Laws.unused.token_lines(Tree.leaves(kids)), Laws.unused.headers(rest)),
      Laws.unused.headers(rest)) : List<&2, U32>}

def unused.def(kids, body, rest, ih):
  +rc = Unused.foreign.opens(Calls.under(kids, body))
  +lc = Laws.unused.imported(kids, body)
  +ra = Unused.lines(Tree.leaves(kids), Unused.foreign(rest))
  +la = List.append(&2, U32, Laws.unused.token_lines(Tree.leaves(kids)), Laws.unused.headers(rest))
  Equal.trans(List<&2, U32>, Bool.pick(List<&2, U32>, rc, ra, Unused.foreign(rest)),
    Bool.pick(List<&2, U32>, lc, ra, Unused.foreign(rest)),
    Bool.pick(List<&2, U32>, lc, la, Laws.unused.headers(rest)),
    Equal.cong(Bool, List<&2, U32>, z => Bool.pick(List<&2, U32>, z, ra, Unused.foreign(rest)), rc, lc,
      unused.opens(Calls.under(kids, body))),
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

# one level of the index: a lookup that goes down bit b2 past a put that went
# down bit b1 reads the put's half when the bits agree, and the half the put
# left alone when they do not
law unused.level:
  for b1: Bool
  for b2: Bool
  for -sub: Unused.Hits
  for -hh: Unused.Hits
  for -rest: Bool
  for -mm: Bool
  for -fs: Unused.Hits -> Bool
  for ih: {fs(sub) == Bool.or(Bool.and(rest, mm), fs(Unused.hits.near(b1, hh))) : Bool}
  {fs(Unused.hits.near(b2, Unused.hits.join(b1, sub, Unused.hits.near(Bool.not(b1), hh))))
    == Bool.or(Bool.and(Bool.and(M4.ix.bit(b1, b2), rest), mm), fs(Unused.hits.near(b2, hh))) : Bool}

def unused.level(b1, b2, _sub, _hh, _rest, _mm, _fs, ih):
  match b1 b2:
    case True{} True{}:
      ih
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      ih

# a lookup after a cell goes in: that cell, when the two lines agree in the
# bits walked and it is the binder asked for, or what was found before
law unused.at:
  for dd: Nat
  for +k1: U32
  for +k2: U32
  for +hh: Unused.Hits
  for +l1: U32
  for +c1: U32
  for +l2: U32
  for +c2: U32
  {Unused.find(Unused.path(dd, k2), Unused.put(Unused.path(dd, k1), hh, Unused.Cell{l1, c1}), l2, c2)
    == Bool.or(Bool.and(M4.ix.bits(dd, k1, k2), Bool.and(U32.is_eq(l1, l2), U32.is_eq(c1, c2))),
      Unused.find(Unused.path(dd, k2), hh, l2, c2)) : Bool}

def unused.at(dd, k1, k2, hh, l1, c1, l2, c2):
  match dd:
    case 0n:
      M3.unused.or(Bool.and(U32.is_eq(l1, l2), U32.is_eq(c1, c2)), Unused.hits.any(Unused.hits.cells(hh), l2, c2),
        Unused.hits.any(Unused.hits.cells(hh), l2, c2), {==})
    case 1n+p:
      unused.level(U32.is_even(k1), U32.is_even(k2),
        Unused.put(Unused.path(p, U32.shr(k1)), Unused.hits.near(U32.is_even(k1), hh), Unused.Cell{l1, c1}), hh,
        M4.ix.bits(p, U32.shr(k1), U32.shr(k2)), Bool.and(U32.is_eq(l1, l2), U32.is_eq(c1, c2)),
        x => Unused.find(Unused.path(p, U32.shr(k2)), x, l2, c2),
        unused.at(p, U32.shr(k1), U32.shr(k2), Unused.hits.near(U32.is_even(k1), hh), l1, c1, l2, c2))

# a cell that is the binder asked for went down the way the lookup walks:
# its line is the line asked, so the two agree in every bit
law unused.alike:
  for +l1: U32
  for +l2: U32
  for -c1: U32
  for -c2: U32
  for e: {Bool.and(U32.is_eq(l1, l2), U32.is_eq(c1, c2)) == True{} : Bool}
  {M4.ix.bits(Unused.depth(), l1, l2) == True{} : Bool}

def unused.alike(l1, l2, c1, c2, e):
  %M5.inert.u32_eq(l1, l2, M4.ix.is_eq(U32.cmp(l1, l2), M5.inert.and_l(U32.is_eq(l1, l2), U32.is_eq(c1, c2), e))) :
    {M4.ix.bits(Unused.depth(), l1, _) == True{} : Bool}
  M4.ix.bits_refl(Unused.depth(), l1)

# the index of the uses is exact: a lookup down a binder's own line finds it
# exactly when a use resolves to it
law unused.exact:
  for uses: List<&2, Bind.Use>
  for +line: U32
  for +col: U32
  {Unused.find(Unused.path(Unused.depth(), line), Unused.index(uses), line, col)
    == Laws.unused.seen(uses, line, col) : Bool}

def unused.exact(uses, line, col):
  match uses:
    case Nil{}:
      unused.none(Unused.path(Unused.depth(), line), line, col)
    case Con{Bind.Use{n, l, c, tg}, +rest}:
      match tg:
        case Bind.TLocal{+tl, +tc}:
          +mm = Bool.and(U32.is_eq(tl, line), U32.is_eq(tc, col))
          +fr = Unused.find(Unused.path(Unused.depth(), line), Unused.index(rest), line, col)
          Equal.trans(Bool,
            Unused.find(Unused.path(Unused.depth(), line),
              Unused.put(Unused.path(Unused.depth(), tl), Unused.index(rest), Unused.Cell{tl, tc}), line, col),
            Bool.or(Bool.and(M4.ix.bits(Unused.depth(), tl, line), mm), fr),
            Bool.or(mm, Laws.unused.seen(rest, line, col)),
            unused.at(Unused.depth(), tl, line, Unused.index(rest), tl, tc, line, col),
            Equal.trans(Bool,
              Bool.or(Bool.and(M4.ix.bits(Unused.depth(), tl, line), mm), fr),
              Bool.or(mm, fr),
              Bool.or(mm, Laws.unused.seen(rest, line, col)),
              Equal.cong(Bool, Bool, z => Bool.or(z, fr), Bool.and(M4.ix.bits(Unused.depth(), tl, line), mm), mm,
                M4.ix.guard(M4.ix.bits(Unused.depth(), tl, line), mm, e => unused.alike(tl, line, tc, col, e))),
              Equal.cong(Bool, Bool, z => Bool.or(mm, z), fr, Laws.unused.seen(rest, line, col),
                unused.exact(rest, line, col))))
        case Bind.TItem{nm}:
          unused.exact(rest, line, col)
        case Bind.TQual{a, nm}:
          unused.exact(rest, line, col)
        case Bind.TFree{}:
          unused.exact(rest, line, col)

# the rule's use search, the index of the uses, is the law's
law unused.seen:
  for +uses: List<&2, Bind.Use>
  for +line: U32
  for +col: U32
  {Unused.seen(Unused.index(uses), line, col) == Laws.unused.seen(uses, line, col) : Bool}

def unused.seen(uses, line, col):
  unused.exact(uses, line, col)

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
      _u => Bool.not(Unused.seen(Unused.index(uses), line, col)))
    == Bool.and(Bool.and(Laws.unused.kept(kk, note, line, fl), Bool.not(String.starts_with(name, "_"))),
      Bool.not(Laws.unused.seen(uses, line, col))) : Bool}

def unused.hit(kk, name, note, line, col, uses, fl):
  +sr = Unused.seen(Unused.index(uses), line, col)
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
  {List.length(&2, F.Finding, Unused.check.go(binds, Unused.index(uses), fl, path))
    == Laws.unused.count(binds, uses, fl) : Nat}

def unused.go(binds, uses, fl, path):
  match binds:
    case Nil{}:
      {==}
    case Con{Bind.Bind{+name, +line, +col, +kk, +note}, +rest}:
      +m = Laws.unused.count(rest, uses, fl)
      +b = Lazy.and_then(Bool.and(Unused.reportable(kk, note, line, fl), Bool.not(String.starts_with(name, "_"))),
        _u => Bool.not(Unused.seen(Unused.index(uses), line, col)))
      Equal.trans(Nat,
        List.length(&2, F.Finding,
          Unused.check.go(Bind.Bind{name, line, col, kk, note} <> rest, Unused.index(uses), fl, path)),
        Bool.pick(Nat, b, 1n+m, m),
        Laws.unused.count(Bind.Bind{name, line, col, kk, note} <> rest, uses, fl),
        M1.nat.pick(b, F.Finding{path, line, col, U32.from_nat(String.length(name)), "unused",
            Unused.what(kk) ++ " " ++ name ++ " is never used."},
          Unused.check.go(rest, Unused.index(uses), fl, path), m, unused.go(rest, uses, fl, path)),
        Equal.cong(Bool, Nat, z => Bool.pick(Nat, z, 1n+m, m), b,
          Bool.and(Bool.and(Laws.unused.kept(kk, note, line, fl), Bool.not(String.starts_with(name, "_"))),
            Bool.not(Laws.unused.seen(uses, line, col))),
          unused.hit(kk, name, note, line, col, uses, fl)))

def Laws.unused_counts(path, _text, _toks, tree, binds, uses, _scopes, _items):
  Equal.trans(Nat,
    List.length(&2, F.Finding, Unused.check.go(binds, Unused.index(uses), Unused.foreign(tree), path)),
    Laws.unused.count(binds, uses, Unused.foreign(tree)),
    Laws.unused.count(binds, uses, Laws.unused.headers(tree)),
    unused.go(binds, uses, Unused.foreign(tree), path),
    Equal.cong(List<&2, U32>, Nat, z => Laws.unused.count(binds, uses, z),
      Unused.foreign(tree), Laws.unused.headers(tree), unused.foreign(tree)))
