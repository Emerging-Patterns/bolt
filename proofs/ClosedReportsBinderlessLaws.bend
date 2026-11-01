# proofs of laws/ClosedReportsBinderlessLaws.bend
import Base
import ../src/finding.bend as F
import ../src/syntax/bind.bend as Bind
import ../src/paths.bend as Paths
import ../src/lazy/lazy.bend as Lazy
import ../src/syntax/tree.bend as Tree
import ../src/rules/correctness/pick.bend as Pick
import ../src/rules/laws/closed.bend as Closed
import ../laws/ClosedReportsBinderlessLaws.bend as Laws
import ./lemmas/Pick.bend as M1

# closed (laws/ClosedReportsBinderlessLaws.bend): the rule's binder test is the law's, and a law
# statement adds a finding exactly when it binds nothing.

# a law's binder test, to the rule and to the law
law closed.binds:
  for body: Tree.Node
  {Closed.binds(body) == Laws.closed.bound(body) : Bool}

def closed.binds(body):
  match body:
    case Tree.NCons{h, rest}:
      match h:
        case Tree.Stmt{kind, _kids, _b}:
          match kind:
            case Tree.SFor{}:
              {==}
            case Tree.SDef{}:
              closed.binds(rest)
            case Tree.SType{}:
              closed.binds(rest)
            case Tree.SLaw{}:
              closed.binds(rest)
            case Tree.SImport{}:
              closed.binds(rest)
            case Tree.SCase{}:
              closed.binds(rest)
            case Tree.SLet{}:
              closed.binds(rest)
            case Tree.STerm{}:
              closed.binds(rest)
        case Tree.Leaf{_x}:
          closed.binds(rest)
        case Tree.Group{_a, _b, _d}:
          closed.binds(rest)
        case Tree.NNil{}:
          closed.binds(rest)
        case Tree.NCons{_a, _b}:
          closed.binds(rest)
    case Tree.Leaf{_x}:
      {==}
    case Tree.Group{_a, _b, _d}:
      {==}
    case Tree.Stmt{_a, _b, _d}:
      {==}
    case Tree.NNil{}:
      {==}

# a finding in front unless b holds adds one to the count
law closed.stop:
  for b: Bool
  for -x: F.Finding
  for -more: List<&2, F.Finding>
  for -m: Nat
  for ih: {List.length(&2, F.Finding, more) == m : Nat}
  {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, b, more, _u => x <> more))
    == Bool.pick(Nat, b, m, 1n+m) : Nat}

def closed.stop(b, _x, more, m, ih):
  match b:
    case True{}:
      ih
    case False{}:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, F.Finding, more), m, ih)

# a top-level law onto a rest the law holds for
law closed.law:
  for +kids: Tree.Node
  for +body: Tree.Node
  for +rest: Tree.Node
  for +path: String
  for ih: {List.length(&2, F.Finding, Closed.check.go(rest, path)) == Laws.closed.count(rest) : Nat}
  {List.length(&2, F.Finding, Closed.check.go(Tree.NCons{Tree.Stmt{Tree.SLaw{}, kids, body}, rest}, path))
    == Laws.closed.count(Tree.NCons{Tree.Stmt{Tree.SLaw{}, kids, body}, rest}) : Nat}

def closed.law(kids, body, rest, path, ih):
  +more = Closed.check.go(rest, path)
  +m = Laws.closed.count(rest)
  +x = {F.Finding{path, Tree.line(kids), Tree.col(kids), 0, "closed",
    "Law " ++ Closed.name.of(Bind.declared(kids))
      ++ " has no `for` or `exs` binder, so it checks a single case; quantify it or delete it."} : F.Finding}
  Equal.trans(Nat,
    List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, Closed.binds(body), more, _u => x <> more)),
    List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, Laws.closed.bound(body), more, _u => x <> more)),
    Bool.pick(Nat, Laws.closed.bound(body), m, 1n+m),
    Equal.cong(Bool, Nat, z => List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, z, more, _u => x <> more)),
      Closed.binds(body), Laws.closed.bound(body), closed.binds(body)),
    closed.stop(Laws.closed.bound(body), x, more, m, ih))

def Laws.closed_walk_counts(root, path):
  match root:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Stmt{kind, +kids, +body}:
          match kind:
            case Tree.SLaw{}:
              closed.law(kids, body, rest, path, Laws.closed_walk_counts(rest, path))
            case Tree.SDef{}:
              Laws.closed_walk_counts(rest, path)
            case Tree.SType{}:
              Laws.closed_walk_counts(rest, path)
            case Tree.SImport{}:
              Laws.closed_walk_counts(rest, path)
            case Tree.SCase{}:
              Laws.closed_walk_counts(rest, path)
            case Tree.SFor{}:
              Laws.closed_walk_counts(rest, path)
            case Tree.SLet{}:
              Laws.closed_walk_counts(rest, path)
            case Tree.STerm{}:
              Laws.closed_walk_counts(rest, path)
        case Tree.Leaf{_x}:
          Laws.closed_walk_counts(rest, path)
        case Tree.Group{_a, _b, _d}:
          Laws.closed_walk_counts(rest, path)
        case Tree.NNil{}:
          Laws.closed_walk_counts(rest, path)
        case Tree.NCons{_a, _b}:
          Laws.closed_walk_counts(rest, path)
    case Tree.Leaf{_x}:
      {==}
    case Tree.Group{_a, _b, _d}:
      {==}
    case Tree.Stmt{_a, _b, _d}:
      {==}
    case Tree.NNil{}:
      {==}

def Laws.closed_counts(path, _text, _toks, tree, _bound, _items):
  Equal.trans(Nat,
    List.length(&2, F.Finding,
      Lazy.stop(List<&2, F.Finding>, Bool.not(Paths.is_laws(path)), [], _u => Closed.check.go(tree, path))),
    Bool.pick(Nat, Bool.not(Paths.is_laws(path)), 0n, Laws.closed.count(tree)),
    Bool.pick(Nat, Paths.is_laws(path), Laws.closed.count(tree), 0n),
    M1.param.stop(Bool.not(Paths.is_laws(path)), Closed.check.go(tree, path), Laws.closed.count(tree),
      Laws.closed_walk_counts(tree, path)),
    M1.arms.flip(Paths.is_laws(path), Laws.closed.count(tree)))
