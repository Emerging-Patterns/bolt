# proofs of laws/InertTranscong.bend
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/syntax/tree.bend as Tree
import ../src/rules/style/transcong.bend as Transcong
import ../laws/InertTranscong.bend as Laws
import ../laws/defs/InertText.bend as D1

# transcong
# ---------

# a name leaf's text, read that way, says what it said: a name is never cut,
# and anything else is no name
law inert.transcong.text:
  for k: Lex.TokKind
  for +t: String
  for +s: String
  {Bool.and(Lex.is_name(k), String.eq(D1.inert.keep(D1.inert.blanks(k), t), s))
    == Bool.and(Lex.is_name(k), String.eq(t, s)) : Bool}

def inert.transcong.text(k, _t, _s):
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

# the rule's name leaf reads a node as it did
law inert.transcong.named:
  for nn: Tree.Node
  for +tt: String
  {Transcong.named(D1.inert.node(nn), tt) == Transcong.named(nn, tt) : Bool}

def inert.transcong.named(nn, tt):
  match nn:
    case Tree.Leaf{tok}:
      match tok:
        case Lex.Tok{k, t, l, c}: inert.transcong.text(k, t, tt)
    case Tree.Group{x, y, z}: {==}
    case Tree.Stmt{x, y, z}: {==}
    case Tree.NNil{}: {==}
    case Tree.NCons{x, y}: {==}

# a group's open is never cut
law inert.transcong.paren:
  for nn: Tree.Node
  {Transcong.paren(D1.inert.node(nn)) == Transcong.paren(nn) : Bool}

def inert.transcong.paren(nn):
  match nn:
    case Tree.Group{open, kids, cl}:
      match open:
        case Lex.Tok{k, o, l, c}: {==}
    case Tree.Leaf{x}: {==}
    case Tree.Stmt{x, y, z}: {==}
    case Tree.NNil{}: {==}
    case Tree.NCons{x, y}: {==}

# a leaf keeps its kind
law inert.transcong.comma:
  for nn: Tree.Node
  {Transcong.comma(D1.inert.node(nn)) == Transcong.comma(nn) : Bool}

def inert.transcong.comma(nn):
  match nn:
    case Tree.Leaf{tok}:
      match tok:
        case Lex.Tok{k, t, l, c}: {==}
    case Tree.Group{x, y, z}: {==}
    case Tree.Stmt{x, y, z}: {==}
    case Tree.NNil{}: {==}
    case Tree.NCons{x, y}: {==}

# an argument ends where it did
law inert.transcong.ends:
  for nn: Tree.Node
  {Transcong.ends(D1.inert.node(nn)) == Transcong.ends(nn) : Bool}

def inert.transcong.ends(nn):
  match nn:
    case Tree.NCons{h, t}: inert.transcong.comma(h)
    case Tree.Leaf{x}: {==}
    case Tree.Group{x, y, z}: {==}
    case Tree.Stmt{x, y, z}: {==}
    case Tree.NNil{}: {==}

# a cong call past its name reads as it did
law inert.transcong.call:
  for nn: Tree.Node
  {Transcong.cong.call(D1.inert.node(nn)) == Transcong.cong.call(nn) : Bool}

def inert.transcong.call(nn):
  match nn:
    case Tree.NCons{+g, +after}:
      %inert.transcong.paren(g) : {Bool.and(Transcong.paren(D1.inert.node(g)), Transcong.ends(D1.inert.node(after)))
        == Bool.and(_, Transcong.ends(after)) : Bool}
      %inert.transcong.ends(after) : {Bool.and(Transcong.paren(D1.inert.node(g)),
          Transcong.ends(D1.inert.node(after)))
        == Bool.and(Transcong.paren(D1.inert.node(g)), _) : Bool}
      {==}
    case Tree.Leaf{x}: {==}
    case Tree.Group{x, y, z}: {==}
    case Tree.Stmt{x, y, z}: {==}
    case Tree.NNil{}: {==}

# a cong argument reads as it did
law inert.transcong.cong:
  for nn: Tree.Node
  {Transcong.cong(D1.inert.node(nn)) == Transcong.cong(nn) : Bool}

def inert.transcong.cong(nn):
  match nn:
    case Tree.NCons{+h, +t}:
      %inert.transcong.named(h, "Equal.cong") : {Bool.and(Transcong.named(D1.inert.node(h), "Equal.cong"),
        Transcong.cong.call(D1.inert.node(t))) == Bool.and(_, Transcong.cong.call(t)) : Bool}
      %inert.transcong.call(t) : {Bool.and(Transcong.named(D1.inert.node(h), "Equal.cong"),
          Transcong.cong.call(D1.inert.node(t)))
        == Bool.and(Transcong.named(D1.inert.node(h), "Equal.cong"), _) : Bool}
      {==}
    case Tree.Leaf{x}: {==}
    case Tree.Group{x, y, z}: {==}
    case Tree.Stmt{x, y, z}: {==}
    case Tree.NNil{}: {==}

# the commas are counted as they were
law inert.transcong.commas:
  for nn: Tree.Node
  {Transcong.commas(D1.inert.node(nn)) == Transcong.commas(nn) : Nat}

def inert.transcong.commas(nn):
  match nn:
    case Tree.NCons{+h, +t}:
      %inert.transcong.comma(h) : {Nat.add(Bool.pick(Nat, Transcong.comma(D1.inert.node(h)), 1n, 0n),
          Transcong.commas(D1.inert.node(t)))
        == Nat.add(Bool.pick(Nat, _, 1n, 0n), Transcong.commas(t)) : Nat}
      %inert.transcong.commas(t) : {Nat.add(Bool.pick(Nat, Transcong.comma(D1.inert.node(h)), 1n, 0n),
          Transcong.commas(D1.inert.node(t)))
        == Nat.add(Bool.pick(Nat, Transcong.comma(D1.inert.node(h)), 1n, 0n), _) : Nat}
      {==}
    case Tree.Leaf{x}: {==}
    case Tree.Group{x, y, z}: {==}
    case Tree.Stmt{x, y, z}: {==}
    case Tree.NNil{}: {==}

# the argument walk reads as it did, from any state
law inert.transcong.fed:
  for nn: Tree.Node
  for +n: Nat
  for +fresh: Bool
  for +seen: Bool
  {Transcong.fed(D1.inert.node(nn), n, fresh, seen) == Transcong.fed(nn, n, fresh, seen) : Bool}

def inert.transcong.fed(nn, n, fresh, seen):
  match nn:
    case Tree.NCons{+h, +t}:
      +lhs = Transcong.fed(D1.inert.node(Tree.NCons{h, t}), n, fresh, seen)
      +late = Transcong.late(n)
      +ih = D1.inert.node(h)
      +it = D1.inert.node(t)
      %inert.transcong.comma(h) : {lhs == Transcong.fed(t, Nat.add(n, Bool.pick(Nat, _, 1n, 0n)), _,
        Bool.or(seen, Bool.and(fresh, Bool.and(late, Transcong.cong(Tree.NCons{h, t}))))) : Bool}
      %inert.transcong.cong(Tree.NCons{h, t}) : {lhs == Transcong.fed(t, Nat.add(n, Bool.pick(Nat,
          Transcong.comma(ih), 1n,
        0n)), Transcong.comma(ih), Bool.or(seen, Bool.and(fresh, Bool.and(late, _)))) : Bool}
      %inert.transcong.fed(t, Nat.add(n, Bool.pick(Nat, Transcong.comma(ih), 1n, 0n)), Transcong.comma(ih),
        Bool.or(seen, Bool.and(fresh, Bool.and(late, Transcong.cong(Tree.NCons{ih, it}))))) : {lhs == _ : Bool}
      {==}
    case Tree.Leaf{x}: {==}
    case Tree.Group{x, y, z}: {==}
    case Tree.Stmt{x, y, z}: {==}
    case Tree.NNil{}: {==}

# the arguments past `Equal.trans` read as they did
law inert.transcong.args:
  for nn: Tree.Node
  {Transcong.args(D1.inert.node(nn)) == Transcong.args(nn) : Bool}

def inert.transcong.args(nn):
  match nn:
    case Tree.NCons{h, after}:
      match h:
        case Tree.Group{open, +kids, cl}:
          match open:
            case Lex.Tok{k, +o, l, c}:
              %inert.transcong.commas(kids) : {Bool.and(String.eq(o, "("), Transcong.shape(D1.inert.node(kids)))
                == Bool.and(String.eq(o, "("), Bool.and(Nat.is_eq(_, 5n), Transcong.fed(kids, 0n, True{},
                    False{}))) : Bool}
              %inert.transcong.fed(kids, 0n, True{}, False{}) : {Bool.and(String.eq(o, "("),
                  Transcong.shape(D1.inert.node(kids)))
                == Bool.and(String.eq(o, "("), Bool.and(Nat.is_eq(Transcong.commas(D1.inert.node(kids)), 5n),
                    _)) : Bool}
              {==}
        case Tree.Leaf{x}: {==}
        case Tree.Stmt{x, y, z}: {==}
        case Tree.NNil{}: {==}
        case Tree.NCons{x, y}: {==}
    case Tree.Leaf{x}: {==}
    case Tree.Group{x, y, z}: {==}
    case Tree.Stmt{x, y, z}: {==}
    case Tree.NNil{}: {==}

# a site reads as it did
law inert.transcong.site:
  for hh: Tree.Node
  for +rest: Tree.Node
  for +path: String
  {Transcong.site(D1.inert.node(hh), D1.inert.node(rest), path) == Transcong.site(hh, rest, path) : List<&2,
      F.Finding>}

def inert.transcong.site(hh, rest, path):
  match hh:
    case Tree.Leaf{tok}:
      match tok:
        case Lex.Tok{+k, +t, +l, +c}:
          +lhs = Transcong.site(D1.inert.node(Tree.Leaf{Lex.Tok{k, t, l, c}}), D1.inert.node(rest), path)
          +f = {[Transcong.cite(l, c, path)] : List<&2, F.Finding>}
          %inert.transcong.text(k, t, "Equal.trans") : {lhs == Bool.pick(List<&2, F.Finding>, Bool.and(_,
              Transcong.args(rest)), f, [])
            : List<&2, F.Finding>}
          %inert.transcong.args(rest) : {lhs == Bool.pick(List<&2, F.Finding>, Bool.and(Bool.and(Lex.is_name(k),
            String.eq(D1.inert.keep(D1.inert.blanks(k), t), "Equal.trans")), _), f, []) : List<&2, F.Finding>}
          {==}
    case Tree.Group{x, y, z}: {==}
    case Tree.Stmt{x, y, z}: {==}
    case Tree.NNil{}: {==}
    case Tree.NCons{x, y}: {==}

# a `=` or `<-` leaf reads as it did: the kind is kept
law inert.transcong.binds:
  for hh: Tree.Node
  {Transcong.binds(D1.inert.node(hh)) == Transcong.binds(hh) : Bool}

def inert.transcong.binds(hh):
  match hh:
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

# the walk reads a node as it did
law inert.transcong.walk:
  for nn: Tree.Node
  for +top: Bool
  for +path: String
  {Transcong.walk(D1.inert.node(nn), top, path) == Transcong.walk(nn, top, path) : List<&2, F.Finding>}

def inert.transcong.walk(nn, top, path):
  match nn:
    case Tree.NCons{+h, +rest}:
      +lhs = Transcong.walk(D1.inert.node(Tree.NCons{h, rest}), top, path)
      +tr = Bool.and(top, Bool.not(Transcong.binds(h)))
      %inert.transcong.site(h, rest, path) : {lhs == List.concat(&2, F.Finding, [Bool.pick(List<&2, F.Finding>, top, _,
          []),
        Transcong.walk(h, True{}, path), Transcong.walk(rest, tr, path)]) : List<&2, F.Finding>}
      %inert.transcong.walk(h, True{}, path) : {lhs == List.concat(&2, F.Finding, [Bool.pick(List<&2, F.Finding>, top,
        Transcong.site(D1.inert.node(h), D1.inert.node(rest), path), []), _, Transcong.walk(rest, tr,
            path)]) : List<&2, F.Finding>}
      %inert.transcong.walk(rest, tr, path) : {lhs == List.concat(&2, F.Finding, [Bool.pick(List<&2, F.Finding>, top,
        Transcong.site(D1.inert.node(h), D1.inert.node(rest), path), []), Transcong.walk(D1.inert.node(h), True{},
            path), _]) : List<&2, F.Finding>}
      %inert.transcong.binds(h) : {lhs == List.concat(&2, F.Finding, [Bool.pick(List<&2, F.Finding>, top,
        Transcong.site(D1.inert.node(h), D1.inert.node(rest), path), []), Transcong.walk(D1.inert.node(h), True{},
            path), Transcong.walk(D1.inert.node(rest), Bool.and(top, Bool.not(_)), path)]) : List<&2, F.Finding>}
      {==}
    case Tree.Group{o, +kids, cl}:
      inert.transcong.walk(kids, True{}, path)
    case Tree.Stmt{+sk, +kids, +body}:
      +tk = Bool.not(Transcong.is_let(sk))
      +lhs = Transcong.walk(D1.inert.node(Tree.Stmt{sk, kids, body}), top, path)
      %inert.transcong.walk(kids, tk, path) : {lhs == List.concat(&2, F.Finding, [_, Transcong.walk(body, True{},
          path)])
        : List<&2, F.Finding>}
      %inert.transcong.walk(body, True{}, path) : {lhs == List.concat(&2, F.Finding,
          [Transcong.walk(D1.inert.node(kids), tk, path),
        _]) : List<&2, F.Finding>}
      {==}
    case Tree.Leaf{tok}:
      {==}
    case Tree.NNil{}:
      {==}

def Laws.inert_transcong(
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
  _ok,
  _ok2,
  e
):
  %inert.transcong.walk(tree, True{}, path) : {_ == Transcong.walk(tree2, True{}, path) : List<&2, F.Finding>}
  %inert.transcong.walk(tree2, True{}, path) : {Transcong.walk(D1.inert.node(tree), True{}, path) == _ : List<&2,
      F.Finding>}
  %e : {Transcong.walk(D1.inert.node(tree), True{}, path) == Transcong.walk(_, True{}, path) : List<&2, F.Finding>}
  {==}
