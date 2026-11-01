# proofs of laws/ForeignReportsMissingBackend.bend
import Base
import ../src/finding.bend as F
import ../src/syntax/bind.bend as Bind
import ../src/lazy/lazy.bend as Lazy
import ../src/syntax/tree.bend as Tree
import ../src/rules/correctness/foreign.bend as Foreign
import ../laws/ForeignReportsMissingBackend.bend as Laws

# foreign (laws/ForeignReportsMissingBackend.bend): the rule's lanes are the law's imports and
# suffixes, its message is empty exactly when the def is not bad, and its
# header test is the law's.

# the early exits of the header test are the plain and and or
law foreign.hd:
  for a: Bool
  for b: Bool
  for -x: Bool
  for -y: Bool
  for ih: {x == y : Bool}
  {Lazy.stop(Bool, Bool.not(a), False{}, _u => Lazy.or_else(b, _v => x)) == Bool.and(a, Bool.or(b, y)) : Bool}

def foreign.hd(a, b, _x, _y, ih):
  match a:
    case False{}:
      {==}
    case True{}:
      match b:
        case True{}:
          {==}
        case False{}:
          ih

def Laws.foreign_native(lines):
  match lines:
    case Nil{}:
      {==}
    case Con{+line, +rest}:
      foreign.hd(String.starts_with(line, "#"), String.eq(line, "# lanes: native"), Foreign.native_only.go(rest),
        Laws.foreign.headed(rest), Laws.foreign_native(rest))

# a body with no more imports ends with the lanes gathered so far
law foreign.done:
  for cc: Bool
  for js: Bool
  {Some{Foreign.Lanes{cc, js}} == Some{Foreign.Lanes{Bool.or(cc, False{}), Bool.or(js, False{})}}
    : Maybe<&2, Foreign.Lanes>}

def foreign.done(cc, js):
  match cc:
    case True{}:
      match js:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      match js:
        case True{}:
          {==}
        case False{}:
          {==}

# gathering a lane early or late gives the same lanes
law foreign.shift:
  for +i: Bool
  for a: Bool
  for +b: Bool
  for +c: Bool
  for d: Bool
  for +e: Bool
  for +f: Bool
  {Bool.pick(Maybe<&2, Foreign.Lanes>, i,
      Some{Foreign.Lanes{Bool.or(Bool.or(a, b), c), Bool.or(Bool.or(d, e), f)}}, None{})
    == Bool.pick(Maybe<&2, Foreign.Lanes>, i,
      Some{Foreign.Lanes{Bool.or(a, Bool.or(b, c)), Bool.or(d, Bool.or(e, f))}}, None{}) : Maybe<&2, Foreign.Lanes>}

def foreign.shift(_i, a, _b, _c, d, _e, _f):
  match a:
    case True{}:
      match d:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      match d:
        case True{}:
          {==}
        case False{}:
          {==}

# the rule's lanes of the imports after the first, onto the lanes so far
law foreign.lgo:
  for body: Tree.Node
  for +cc: Bool
  for +js: Bool
  {Foreign.lanes.go(body, cc, js)
    == Bool.pick(Maybe<&2, Foreign.Lanes>, Laws.foreign.imports(body),
      Some{Foreign.Lanes{Bool.or(cc, Laws.foreign.has(body, ".c\"")), Bool.or(js, Laws.foreign.has(body, ".js\""))}},
      None{}) : Maybe<&2, Foreign.Lanes>}

def foreign.lgo(body, cc, js):
  match body:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Stmt{kind, +kids, ib}:
          match kind:
            case Tree.SImport{}:
              +ec = String.ends_with(Foreign.target(kids), ".c\"")
              +ej = String.ends_with(Foreign.target(kids), ".js\"")
              Equal.trans(Maybe<&2, Foreign.Lanes>, Foreign.lanes.go(rest, Bool.or(cc, ec), Bool.or(js, ej)),
                Bool.pick(Maybe<&2, Foreign.Lanes>, Laws.foreign.imports(rest),
                  Some{Foreign.Lanes{Bool.or(Bool.or(cc, ec), Laws.foreign.has(rest, ".c\"")),
                    Bool.or(Bool.or(js, ej), Laws.foreign.has(rest, ".js\""))}}, None{}),
                Bool.pick(Maybe<&2, Foreign.Lanes>, Laws.foreign.imports(rest),
                  Some{Foreign.Lanes{Bool.or(cc, Bool.or(ec, Laws.foreign.has(rest, ".c\""))),
                    Bool.or(js, Bool.or(ej, Laws.foreign.has(rest, ".js\"")))}}, None{}),
                foreign.lgo(rest, Bool.or(cc, ec), Bool.or(js, ej)),
                foreign.shift(Laws.foreign.imports(rest), cc, ec, Laws.foreign.has(rest, ".c\""), js, ej,
                  Laws.foreign.has(rest, ".js\"")))
            case Tree.SDef{}:
              {==}
            case Tree.SType{}:
              {==}
            case Tree.SLaw{}:
              {==}
            case Tree.SCase{}:
              {==}
            case Tree.SFor{}:
              {==}
            case Tree.SLet{}:
              {==}
            case Tree.STerm{}:
              {==}
        case Tree.Leaf{x}:
          {==}
        case Tree.Group{a, b, d}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{a, b}:
          {==}
    case Tree.Leaf{x}:
      foreign.done(cc, js)
    case Tree.Group{a, b, d}:
      foreign.done(cc, js)
    case Tree.Stmt{a, b, d}:
      foreign.done(cc, js)
    case Tree.NNil{}:
      foreign.done(cc, js)

# the rule's lanes of a def's body: the law's lanes of a foreign def, else none
law foreign.lanes:
  for body: Tree.Node
  {Foreign.lanes(body)
    == Bool.pick(Maybe<&2, Foreign.Lanes>, Laws.foreign.only(body),
      Some{Foreign.Lanes{Laws.foreign.has(body, ".c\""), Laws.foreign.has(body, ".js\"")}}, None{})
    : Maybe<&2, Foreign.Lanes>}

def foreign.lanes(body):
  match body:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Stmt{kind, +kids, ib}:
          match kind:
            case Tree.SImport{}:
              foreign.lgo(rest, String.ends_with(Foreign.target(kids), ".c\""),
                String.ends_with(Foreign.target(kids), ".js\""))
            case Tree.SDef{}:
              {==}
            case Tree.SType{}:
              {==}
            case Tree.SLaw{}:
              {==}
            case Tree.SCase{}:
              {==}
            case Tree.SFor{}:
              {==}
            case Tree.SLet{}:
              {==}
            case Tree.STerm{}:
              {==}
        case Tree.Leaf{x}:
          {==}
        case Tree.Group{a, b, d}:
          {==}
        case Tree.NNil{}:
          {==}
        case Tree.NCons{a, b}:
          {==}
    case Tree.Leaf{x}:
      {==}
    case Tree.Group{a, b, d}:
      {==}
    case Tree.Stmt{a, b, d}:
      {==}
    case Tree.NNil{}:
      {==}

# the rule's message is empty exactly when the lanes are not bad
law foreign.lack:
  for o: Bool
  for c: Bool
  for j: Bool
  for native: Bool
  for +nm: String
  {String.is_empty(Foreign.lack(Bool.pick(Maybe<&2, Foreign.Lanes>, o, Some{Foreign.Lanes{c, j}}, None{}), native, nm))
    == Bool.not(Bool.and(o, Bool.or(Bool.and(c, Bool.and(Bool.not(j), Bool.not(native))), Bool.and(j, Bool.not(c)))))
    : Bool}

def foreign.lack(o, c, j, native, _nm):
  match o:
    case False{}:
      {==}
    case True{}:
      match c:
        case True{}:
          match j:
            case True{}:
              match native:
                case True{}:
                  {==}
                case False{}:
                  {==}
            case False{}:
              match native:
                case True{}:
                  {==}
                case False{}:
                  {==}
        case False{}:
          match j:
            case True{}:
              match native:
                case True{}:
                  {==}
                case False{}:
                  {==}
            case False{}:
              match native:
                case True{}:
                  {==}
                case False{}:
                  {==}

# a finding in front unless the message is empty adds one to the count
law foreign.at2:
  for bad: Bool
  for -x: F.Finding
  for -more: List<&2, F.Finding>
  for -m: Nat
  for ih: {List.length(&2, F.Finding, more) == m : Nat}
  {List.length(&2, F.Finding, Bool.pick(List<&2, F.Finding>, Bool.not(bad), more, x <> more))
    == Bool.pick(Nat, bad, 1n+m, m) : Nat}

def foreign.at2(bad, _x, more, m, ih):
  match bad:
    case True{}:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, F.Finding, more), m, ih)
    case False{}:
      ih

# a top-level def onto a rest the law holds for
law foreign.def:
  for +kids: Tree.Node
  for +body: Tree.Node
  for +rest: Tree.Node
  for +native: Bool
  for +path: String
  for ih: {List.length(&2, F.Finding, Foreign.check.go(rest, native, path)) == Laws.foreign.count(rest, native) : Nat}
  {List.length(&2, F.Finding, Foreign.check.go(Tree.NCons{Tree.Stmt{Tree.SDef{}, kids, body}, rest}, native, path))
    == Laws.foreign.count(Tree.NCons{Tree.Stmt{Tree.SDef{}, kids, body}, rest}, native) : Nat}

def foreign.def(kids, body, rest, native, path, ih):
  +nm = Foreign.name.of(Bind.declared(kids))
  +msg = Foreign.lack(Foreign.lanes(body), native, nm)
  +more = Foreign.check.go(rest, native, path)
  +bad = Laws.foreign.bad(body, native)
  +x = {F.Finding{path, Tree.line(kids), Tree.col(kids), 0, "foreign", msg} : F.Finding}
  +e = Equal.trans(Bool, String.is_empty(msg),
    String.is_empty(Foreign.lack(Bool.pick(Maybe<&2, Foreign.Lanes>, Laws.foreign.only(body),
      Some{Foreign.Lanes{Laws.foreign.has(body, ".c\""), Laws.foreign.has(body, ".js\"")}}, None{}), native, nm)),
    Bool.not(bad),
    Equal.cong(Maybe<&2, Foreign.Lanes>, Bool, z => String.is_empty(Foreign.lack(z, native, nm)), Foreign.lanes(body),
      Bool.pick(Maybe<&2, Foreign.Lanes>, Laws.foreign.only(body),
        Some{Foreign.Lanes{Laws.foreign.has(body, ".c\""), Laws.foreign.has(body, ".js\"")}}, None{}),
      foreign.lanes(body)),
    foreign.lack(Laws.foreign.only(body), Laws.foreign.has(body, ".c\""), Laws.foreign.has(body, ".js\""), native, nm))
  Equal.trans(Nat, List.length(&2, F.Finding, Bool.pick(List<&2, F.Finding>, String.is_empty(msg), more, x <> more)),
    List.length(&2, F.Finding, Bool.pick(List<&2, F.Finding>, Bool.not(bad), more, x <> more)),
    Bool.pick(Nat, bad, 1n+Laws.foreign.count(rest, native), Laws.foreign.count(rest, native)),
    Equal.cong(Bool, Nat, z => List.length(&2, F.Finding, Bool.pick(List<&2, F.Finding>, z, more, x <> more)),
      String.is_empty(msg), Bool.not(bad), e),
    foreign.at2(bad, x, more, Laws.foreign.count(rest, native), ih))

def Laws.foreign_walk_counts(root, native, path):
  match root:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Stmt{kind, +kids, +body}:
          match kind:
            case Tree.SDef{}:
              foreign.def(kids, body, rest, native, path, Laws.foreign_walk_counts(rest, native, path))
            case Tree.SType{}:
              Laws.foreign_walk_counts(rest, native, path)
            case Tree.SLaw{}:
              Laws.foreign_walk_counts(rest, native, path)
            case Tree.SImport{}:
              Laws.foreign_walk_counts(rest, native, path)
            case Tree.SCase{}:
              Laws.foreign_walk_counts(rest, native, path)
            case Tree.SFor{}:
              Laws.foreign_walk_counts(rest, native, path)
            case Tree.SLet{}:
              Laws.foreign_walk_counts(rest, native, path)
            case Tree.STerm{}:
              Laws.foreign_walk_counts(rest, native, path)
        case Tree.Leaf{x}:
          Laws.foreign_walk_counts(rest, native, path)
        case Tree.Group{a, b, d}:
          Laws.foreign_walk_counts(rest, native, path)
        case Tree.NNil{}:
          Laws.foreign_walk_counts(rest, native, path)
        case Tree.NCons{a, b}:
          Laws.foreign_walk_counts(rest, native, path)
    case Tree.Leaf{x}:
      {==}
    case Tree.Group{a, b, d}:
      {==}
    case Tree.Stmt{a, b, d}:
      {==}
    case Tree.NNil{}:
      {==}

def Laws.foreign_counts(path, text, _toks, tree, _bound, _items):
  Equal.trans(Nat, List.length(&2, F.Finding, Foreign.check.go(tree, Foreign.native_only(text), path)),
    Laws.foreign.count(tree, Foreign.native_only(text)),
    Laws.foreign.count(tree, Laws.foreign.headed(String.lines(text))),
    Laws.foreign_walk_counts(tree, Foreign.native_only(text), path),
    Equal.cong(Bool, Nat, z => Laws.foreign.count(tree, z), Foreign.native_only(text),
      Laws.foreign.headed(String.lines(text)), Laws.foreign_native(String.lines(text))))
