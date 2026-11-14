# proofs of laws/TranscongReportsTransCongChains.bend
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/syntax/tree.bend as Tree
import ../src/rules/correctness/pick.bend as Pick
import ../src/rules/style/transcong.bend as Transcong
import ../laws/TranscongReportsTransCongChains.bend as Laws
import ./lemmas/Pick.bend as M1

# transcong (laws/TranscongReportsTransCongChains.bend). Each helper of the rule agrees with the law's by
# one split, the comma count and the argument walk by induction; a site then
# gives one finding exactly when the law's site test holds, and the walk adds
# up as thunk's does.

# the rule's name leaf is the law's
law transcong.name:
  for n: Tree.Node
  for +t: String
  {Transcong.named(n, t) == Laws.transcong.name(n, t) : Bool}

def transcong.name(n, _tt):
  match n:
    case Tree.Leaf{tok}:
      match tok:
        case Lex.Tok{k, t, l, c}: {==}
    case Tree.Group{x, y, z}: {==}
    case Tree.Stmt{x, y, z}: {==}
    case Tree.NNil{}: {==}
    case Tree.NCons{x, y}: {==}

# the rule's `(` group is the law's
law transcong.open:
  for n: Tree.Node
  {Transcong.paren(n) == Laws.transcong.open(n) : Bool}

def transcong.open(n):
  match n:
    case Tree.Group{open, kids, cl}:
      match open:
        case Lex.Tok{k, o, l, c}: {==}
    case Tree.Leaf{x}: {==}
    case Tree.Stmt{x, y, z}: {==}
    case Tree.NNil{}: {==}
    case Tree.NCons{x, y}: {==}

# the rule's comma leaf is the law's
law transcong.comma:
  for n: Tree.Node
  {Transcong.comma(n) == Laws.transcong.comma(n) : Bool}

def transcong.comma(n):
  match n:
    case Tree.Leaf{tok}:
      match tok:
        case Lex.Tok{k, t, l, c}: {==}
    case Tree.Group{x, y, z}: {==}
    case Tree.Stmt{x, y, z}: {==}
    case Tree.NNil{}: {==}
    case Tree.NCons{x, y}: {==}

# the rule's end of an argument is the law's
law transcong.last:
  for n: Tree.Node
  {Transcong.ends(n) == Laws.transcong.last(n) : Bool}

def transcong.last(n):
  match n:
    case Tree.NCons{h, t}: transcong.comma(h)
    case Tree.Leaf{x}: {==}
    case Tree.Group{x, y, z}: {==}
    case Tree.Stmt{x, y, z}: {==}
    case Tree.NNil{}: {==}

# the rule's cong call past its name is the law's
law transcong.call:
  for n: Tree.Node
  {Transcong.cong.call(n) == Laws.transcong.call(n) : Bool}

def transcong.call(n):
  match n:
    case Tree.NCons{+g, +after}:
      %transcong.open(g) : {Bool.and(Transcong.paren(g), Transcong.ends(after)) == Bool.and(_,
          Laws.transcong.last(after))
        : Bool}
      %transcong.last(after) : {Bool.and(Transcong.paren(g), Transcong.ends(after)) == Bool.and(Transcong.paren(g),
          _) : Bool}
      {==}
    case Tree.Leaf{x}: {==}
    case Tree.Group{x, y, z}: {==}
    case Tree.Stmt{x, y, z}: {==}
    case Tree.NNil{}: {==}

# the rule's cong argument is the law's
law transcong.cong:
  for n: Tree.Node
  {Transcong.cong(n) == Laws.transcong.cong(n) : Bool}

def transcong.cong(n):
  match n:
    case Tree.NCons{+h, +t}:
      %transcong.name(h, "Equal.cong") : {Bool.and(Transcong.named(h, "Equal.cong"), Transcong.cong.call(t))
        == Bool.and(_, Laws.transcong.call(t)) : Bool}
      %transcong.call(t) : {Bool.and(Transcong.named(h, "Equal.cong"), Transcong.cong.call(t))
        == Bool.and(Transcong.named(h, "Equal.cong"), _) : Bool}
      {==}
    case Tree.Leaf{x}: {==}
    case Tree.Group{x, y, z}: {==}
    case Tree.Stmt{x, y, z}: {==}
    case Tree.NNil{}: {==}

# the rule's comma count is the law's
law transcong.commas:
  for n: Tree.Node
  {Transcong.commas(n) == Laws.transcong.commas(n) : Nat}

def transcong.commas(nn):
  match nn:
    case Tree.NCons{+h, +t}:
      %transcong.comma(h) : {Nat.add(Bool.pick(Nat, Transcong.comma(h), 1n, 0n), Transcong.commas(t))
        == Nat.add(Bool.pick(Nat, _, 1n, 0n), Laws.transcong.commas(t)) : Nat}
      %transcong.commas(t) : {Nat.add(Bool.pick(Nat, Transcong.comma(h), 1n, 0n), Transcong.commas(t))
        == Nat.add(Bool.pick(Nat, Transcong.comma(h), 1n, 0n), _) : Nat}
      {==}
    case Tree.Leaf{x}: {==}
    case Tree.Group{x, y, z}: {==}
    case Tree.Stmt{x, y, z}: {==}
    case Tree.NNil{}: {==}

# the rule's argument walk is the law's, from any state
law transcong.fed:
  for nn: Tree.Node
  for +n: Nat
  for +fresh: Bool
  for +seen: Bool
  {Transcong.fed(nn, n, fresh, seen) == Laws.transcong.fed(nn, n, fresh, seen) : Bool}

def transcong.fed(nn, n, fresh, seen):
  match nn:
    case Tree.NCons{+h, +t}:
      +lhs = Transcong.fed(Tree.NCons{h, t}, n, fresh, seen)
      +late = Bool.or(Nat.is_eq(n, 4n), Nat.is_eq(n, 5n))
      %transcong.comma(h) : {lhs == Laws.transcong.fed(t, Nat.add(n, Bool.pick(Nat, _, 1n, 0n)), _,
        Bool.or(seen, Bool.and(fresh, Bool.and(late, Laws.transcong.cong(Tree.NCons{h, t}))))) : Bool}
      %transcong.cong(Tree.NCons{h, t}) : {lhs == Laws.transcong.fed(t, Nat.add(n, Bool.pick(Nat, Transcong.comma(h),
          1n,
          0n)),
        Transcong.comma(h), Bool.or(seen, Bool.and(fresh, Bool.and(late, _)))) : Bool}
      %transcong.fed(t, Nat.add(n, Bool.pick(Nat, Transcong.comma(h), 1n, 0n)), Transcong.comma(h),
        Bool.or(seen, Bool.and(fresh, Bool.and(late, Transcong.cong(Tree.NCons{h, t}))))) : {lhs == _ : Bool}
      {==}
    case Tree.Leaf{x}: {==}
    case Tree.Group{x, y, z}: {==}
    case Tree.Stmt{x, y, z}: {==}
    case Tree.NNil{}: {==}

# the rule's arguments past `Equal.trans` are the law's
law transcong.args:
  for n: Tree.Node
  {Transcong.args(n) == Laws.transcong.args(n) : Bool}

def transcong.args(nn):
  match nn:
    case Tree.NCons{h, after}:
      match h:
        case Tree.Group{open, +kids, cl}:
          match open:
            case Lex.Tok{k, +o, l, c}:
              %transcong.commas(kids) : {Bool.and(String.eq(o, "("), Transcong.shape(kids)) == Bool.and(String.eq(o,
                  "("),
                Bool.and(Nat.is_eq(_, 5n), Laws.transcong.fed(kids, 0n, True{}, False{}))) : Bool}
              %transcong.fed(kids, 0n, True{}, False{}) : {Bool.and(String.eq(o, "("), Transcong.shape(kids))
                == Bool.and(String.eq(o, "("), Bool.and(Nat.is_eq(Transcong.commas(kids), 5n), _)) : Bool}
              {==}
        case Tree.Leaf{x}: {==}
        case Tree.Stmt{x, y, z}: {==}
        case Tree.NNil{}: {==}
        case Tree.NCons{x, y}: {==}
    case Tree.Leaf{x}: {==}
    case Tree.Group{x, y, z}: {==}
    case Tree.Stmt{x, y, z}: {==}
    case Tree.NNil{}: {==}

# a site: the rule's finding is the law's count
law transcong.site:
  for h: Tree.Node
  for +rest: Tree.Node
  for +path: String
  {List.length(&2, F.Finding, Transcong.site(h, rest, path)) == Bool.pick(Nat, Laws.transcong.at(h, rest), 1n,
      0n) : Nat}

def transcong.site(h, rest, path):
  match h:
    case Tree.Leaf{tok}:
      match tok:
        case Lex.Tok{+k, +t, l, c}:
          +f = Transcong.cite(l, c, path)
          +b = Bool.and(Bool.and(Lex.is_name(k), String.eq(t, "Equal.trans")), Transcong.args(rest))
          %transcong.args(rest) : {List.length(&2, F.Finding, Bool.pick(List<&2, F.Finding>, b, [f], []))
            == Bool.pick(Nat, Bool.and(Bool.and(Lex.is_name(k), String.eq(t, "Equal.trans")), _), 1n, 0n) : Nat}
          M1.thunk.one(b, f)
    case Tree.Group{x, y, z}: {==}
    case Tree.Stmt{x, y, z}: {==}
    case Tree.NNil{}: {==}
    case Tree.NCons{x, y}: {==}

# a site gated by top: the rule's finding is the law's count
law transcong.gate:
  for +top: Bool
  for h: Tree.Node
  for +rest: Tree.Node
  for +path: String
  {List.length(&2, F.Finding, Bool.pick(List<&2, F.Finding>, top, Transcong.site(h, rest, path), []))
    == Bool.pick(Nat, Bool.and(top, Laws.transcong.at(h, rest)), 1n, 0n) : Nat}

def transcong.gate(top, h, rest, path):
  match top:
    case True{}: transcong.site(h, rest, path)
    case False{}: {==}

# the rule's let is the law's
law transcong.let:
  for sk: Tree.StmtKind
  {Transcong.is_let(sk) == Laws.transcong.let(sk) : Bool}

def transcong.let(sk):
  match sk:
    case Tree.SDef{}: {==}
    case Tree.SType{}: {==}
    case Tree.SLaw{}: {==}
    case Tree.SImport{}: {==}
    case Tree.SCase{}: {==}
    case Tree.SFor{}: {==}
    case Tree.SLet{}: {==}
    case Tree.STerm{}: {==}

# the rule's `=` / `<-` leaf is the law's
law transcong.binds:
  for n: Tree.Node
  {Transcong.binds(n) == Laws.transcong.binds(n) : Bool}

def transcong.binds(n):
  match n:
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
    case Tree.Group{x, y, z}: {==}
    case Tree.Stmt{x, y, z}: {==}
    case Tree.NNil{}: {==}
    case Tree.NCons{x, y}: {==}

def Laws.transcong_walk_counts(nn, top, path):
  match nn:
    case Tree.NCons{+h, +rest}:
      +tr = Bool.and(top, Bool.not(Transcong.binds(h)))
      %transcong.binds(h) : {List.length(&2, F.Finding, List.concat(&2, F.Finding,
        [Bool.pick(List<&2, F.Finding>, top, Transcong.site(h, rest, path), []), Transcong.walk(h, True{}, path),
          Transcong.walk(rest, tr, path)]))
        == Nat.add(Bool.pick(Nat, Bool.and(top, Laws.transcong.at(h, rest)), 1n, 0n),
          Nat.add(Laws.transcong.count(h, True{}), Laws.transcong.count(rest, Bool.and(top, Bool.not(_))))) : Nat}
      M1.table.three(Bool.pick(List<&2, F.Finding>, top, Transcong.site(h, rest, path), []),
        Transcong.walk(h, True{}, path), Transcong.walk(rest, tr, path),
        Bool.pick(Nat, Bool.and(top, Laws.transcong.at(h, rest)), 1n, 0n),
        Laws.transcong.count(h, True{}), Laws.transcong.count(rest, tr), transcong.gate(top, h, rest, path),
        Laws.transcong_walk_counts(h, True{}, path), Laws.transcong_walk_counts(rest, tr, path))
    case Tree.Group{o, +kids, cl}:
      Laws.transcong_walk_counts(kids, True{}, path)
    case Tree.Stmt{+sk, +kids, +body}:
      +tk = Bool.not(Transcong.is_let(sk))
      %transcong.let(sk) : {List.length(&2, F.Finding, List.concat(&2, F.Finding, [Transcong.walk(kids, tk, path),
        Transcong.walk(body, True{}, path)])) == Nat.add(Laws.transcong.count(kids, Bool.not(_)),
        Laws.transcong.count(body, True{})) : Nat}
      M1.table.two(Transcong.walk(kids, tk, path), Transcong.walk(body, True{}, path), Laws.transcong.count(kids, tk),
        Laws.transcong.count(body, True{}), Laws.transcong_walk_counts(kids, tk, path),
        Laws.transcong_walk_counts(body, True{}, path))
    case Tree.Leaf{tok}:
      {==}
    case Tree.NNil{}:
      {==}

def Laws.transcong_counts(path, _text, _toks, tree, _bound, _items):
  Laws.transcong_walk_counts(tree, True{}, path)
