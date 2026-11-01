# proofs of laws/ScanReportsCarriedArgumentWalks.bend
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/paths.bend as Paths
import ../src/lazy/lazy.bend as Lazy
import ../src/syntax/tree.bend as Tree
import ../src/rules/calls.bend as Calls
import ../src/rules/suspicious/hoist.bend as Hoist
import ../src/rules/suspicious/scan.bend as Scan
import ../laws/ScanReportsCarriedArgumentWalks.bend as Laws
import ./lemmas/MatchStatementCounts.bend as M1

# the file's walks of a name are the law's
law scan.file_at:
  for ws: List<&2, Scan.Walk>
  for +tt: String
  {Scan.file_at(ws, tt) == Laws.scan.file(ws, tt) : List<&2, Nat>}

def scan.file_at(ws, tt):
  match ws:
    case Nil{}:
      {==}
    case Con{Scan.Walk{+nm, +at}, +rest}:
      %scan.file_at(rest, tt) : {Scan.file_at(Scan.Walk{nm, at} <> rest, tt)
        == Bool.pick(List<&2, Nat>, String.eq(nm, tt), at <> _, _) : List<&2, Nat>}
      {==}

def Laws.scan_slots(tt, ws):
  %scan.file_at(ws, tt) : {Scan.slots(tt, ws) == List.append(&2, Nat, Laws.scan.base(tt), _) : List<&2, Nat>}
  {==}

# three finding lists, each empty, join empty
law scan.nil3:
  for -a: List<&2, F.Finding>
  for -b: List<&2, F.Finding>
  for -c: List<&2, F.Finding>
  for ea: {a == Nil{} : List<&2, F.Finding>}
  for eb: {b == Nil{} : List<&2, F.Finding>}
  for ec: {c == Nil{} : List<&2, F.Finding>}
  {List.concat(&2, F.Finding, [a, b, c]) == Nil{} : List<&2, F.Finding>}

def scan.nil3(a, b, c, ea, eb, ec):
  %Equal.sym(List<&2, F.Finding>, a, Nil{}, ea) : {List.concat(&2, F.Finding, [_, b, c]) == Nil{}
    : List<&2, F.Finding>}
  %Equal.sym(List<&2, F.Finding>, b, Nil{}, eb) : {List.concat(&2, F.Finding, [Nil{}, _, c]) == Nil{}
    : List<&2, F.Finding>}
  %Equal.sym(List<&2, F.Finding>, c, Nil{}, ec) : {List.concat(&2, F.Finding, [Nil{}, Nil{}, _]) == Nil{}
    : List<&2, F.Finding>}
  {==}

# two finding lists, each empty, join empty
law scan.nil2:
  for -a: List<&2, F.Finding>
  for -b: List<&2, F.Finding>
  for ea: {a == Nil{} : List<&2, F.Finding>}
  for eb: {b == Nil{} : List<&2, F.Finding>}
  {List.concat(&2, F.Finding, [a, b]) == Nil{} : List<&2, F.Finding>}

def scan.nil2(a, b, ea, eb):
  %Equal.sym(List<&2, F.Finding>, a, Nil{}, ea) : {List.concat(&2, F.Finding, [_, b]) == Nil{} : List<&2, F.Finding>}
  %Equal.sym(List<&2, F.Finding>, b, Nil{}, eb) : {List.concat(&2, F.Finding, [Nil{}, _]) == Nil{}
    : List<&2, F.Finding>}
  {==}

# no name is kept against no names
law scan.keep_nil:
  for mm: Maybe<&2, String>
  {Scan.keep_in(mm, []) == None{} : Maybe<&2, String>}

def scan.keep_nil(mm):
  match mm:
    case None{}:
      {==}
    case Some{nm}:
      {==}

# no walked argument is one of no names
law scan.found_nil:
  for ss: List<&2, Nat>
  for +as: List<&2, Tree.Node>
  {Scan.found(ss, as, []) == None{} : Maybe<&2, String>}

def scan.found_nil(ss, as):
  match ss:
    case Nil{}:
      {==}
    case Con{+at, +rest}:
      %Equal.sym(Maybe<&2, String>, Scan.keep_in(Scan.name_of(Calls.arg(as, at)), []), None{},
        scan.keep_nil(Scan.name_of(Calls.arg(as, at)))) : {Scan.first(_, Scan.found(rest, as, [])) == None{}
          : Maybe<&2, String>}
      scan.found_nil(rest, as)

# a stop that gives nothing either way gives nothing
law scan.stop_nil:
  for c: Bool
  {Lazy.stop(List<&2, F.Finding>, c, [], _u => Nil{}) == Nil{} : List<&2, F.Finding>}

def scan.stop_nil(c):
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

# a named call reports nothing when nothing is carried
law scan.on_nil:
  for +hot: Bool
  for +open: Bool
  for +tt: String
  for +line: U32
  for +col: U32
  for +kids: Tree.Node
  for +self: String
  for +ws: List<&2, Scan.Walk>
  for +lead: String
  for +path: String
  {Scan.on_name(hot, open, tt, line, col, kids, self, ws, [], lead, path) == Nil{} : List<&2, F.Finding>}

def scan.on_nil(hot, open, tt, line, col, kids, self, ws, lead, path):
  %Equal.sym(Maybe<&2, String>, Scan.found(Scan.slots(tt, ws), Calls.args(kids), []), None{},
    scan.found_nil(Scan.slots(tt, ws), Calls.args(kids))) : {Lazy.stop(List<&2, F.Finding>,
      Bool.not(Bool.and(hot, Bool.and(open, Bool.not(String.eq(tt, self))))), [],
      _u => Scan.cite(_, tt, line, col, self, lead, path)) == Nil{} : List<&2, F.Finding>}
  scan.stop_nil(Bool.not(Bool.and(hot, Bool.and(open, Bool.not(String.eq(tt, self))))))

# a call reports nothing when nothing is carried, whatever its callee's kind
law scan.hit_nil:
  for kk: Lex.TokKind
  for +hot: Bool
  for +open: Bool
  for +tt: String
  for +line: U32
  for +col: U32
  for +kids: Tree.Node
  for +self: String
  for +ws: List<&2, Scan.Walk>
  for +lead: String
  for +path: String
  {Scan.call_hit(kk, hot, open, tt, line, col, kids, self, ws, [], lead, path) == Nil{} : List<&2, F.Finding>}

def scan.hit_nil(kk, hot, open, tt, line, col, kids, self, ws, lead, path):
  match kk:
    case Lex.TName{}:
      scan.on_nil(hot, open, tt, line, col, kids, self, ws, lead, path)
    case Lex.TUpper{}:
      {==}
    case Lex.TDotted{}:
      scan.on_nil(hot, open, tt, line, col, kids, self, ws, lead, path)
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

def Laws.scan_quiet(nn, self, ws, lead, path, hot):
  match nn:
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
        case Tree.Leaf{Lex.Tok{+k, +t, +l, +c}}:
          match rest:
            case Tree.Leaf{tok}:
              {==}
            case Tree.Group{o, gk, cl}:
              {==}
            case Tree.Stmt{kind, sk, sb}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{rh, +rr}:
              match rh:
                case Tree.Group{Lex.Tok{gk, +o, gl, gc}, +kids, cl}:
                  scan.nil3(Scan.call_hit(k, Hoist.warm(hot, k), String.eq(o, "("), t, l, c, kids, self, ws, [], lead,
                      path),
                    Scan.walk(kids, self, ws, [], lead, path, Hoist.warm(hot, k)),
                    Scan.walk(rr, self, ws, [], lead, path, Hoist.warm(hot, k)),
                    scan.hit_nil(k, Hoist.warm(hot, k), String.eq(o, "("), t, l, c, kids, self, ws, lead, path),
                    Laws.scan_quiet(kids, self, ws, lead, path, Hoist.warm(hot, k)), Laws.scan_quiet(rr, self, ws,
                        lead, path, Hoist.warm(hot, k)))
                case Tree.Leaf{tok}:
                  Laws.scan_quiet(rest, self, ws, lead, path, Hoist.warm(hot, k))
                case Tree.Stmt{kind, sk, sb}:
                  Laws.scan_quiet(rest, self, ws, lead, path, Hoist.warm(hot, k))
                case Tree.NNil{}:
                  Laws.scan_quiet(rest, self, ws, lead, path, Hoist.warm(hot, k))
                case Tree.NCons{nh, nt}:
                  Laws.scan_quiet(rest, self, ws, lead, path, Hoist.warm(hot, k))
        case Tree.Group{o, +kids, cl}:
          scan.nil2(Scan.walk(kids, self, ws, [], lead, path, hot), Scan.walk(rest, self, ws, [], lead, path, hot),
              Laws.scan_quiet(kids, self, ws, lead, path, hot), Laws.scan_quiet(rest, self, ws, lead, path, hot))
        case Tree.Stmt{kind, +kids, +body}:
          match kind:
            case Tree.SDef{}:
              scan.nil3(Scan.walk(kids, self, ws, [], lead, path, hot), Scan.walk(body, self, ws, [], lead, path, hot),
                  Scan.walk(rest, self, ws, [], lead, path, hot),
                Laws.scan_quiet(kids, self, ws, lead, path, hot), Laws.scan_quiet(body, self, ws, lead, path,
                    hot), Laws.scan_quiet(rest, self, ws, lead, path, hot))
            case Tree.SType{}:
              scan.nil3(Scan.walk(kids, self, ws, [], lead, path, hot), Scan.walk(body, self, ws, [], lead, path, hot),
                  Scan.walk(rest, self, ws, [], lead, path, hot),
                Laws.scan_quiet(kids, self, ws, lead, path, hot), Laws.scan_quiet(body, self, ws, lead, path,
                    hot), Laws.scan_quiet(rest, self, ws, lead, path, hot))
            case Tree.SLaw{}:
              scan.nil3(Scan.walk(kids, self, ws, [], lead, path, hot), Scan.walk(body, self, ws, [], lead, path, hot),
                  Scan.walk(rest, self, ws, [], lead, path, hot),
                Laws.scan_quiet(kids, self, ws, lead, path, hot), Laws.scan_quiet(body, self, ws, lead, path,
                    hot), Laws.scan_quiet(rest, self, ws, lead, path, hot))
            case Tree.SImport{}:
              scan.nil3(Scan.walk(kids, self, ws, [], lead, path, hot), Scan.walk(body, self, ws, [], lead, path, hot),
                  Scan.walk(rest, self, ws, [], lead, path, hot),
                Laws.scan_quiet(kids, self, ws, lead, path, hot), Laws.scan_quiet(body, self, ws, lead, path,
                    hot), Laws.scan_quiet(rest, self, ws, lead, path, hot))
            case Tree.SCase{}:
              scan.nil3(Scan.walk(kids, self, ws, [], lead, path, False{}), Scan.walk(body, self, ws, [], lead, path,
                  Bool.and(hot, Calls.calls(body, self))), Scan.walk(rest, self, ws, [], lead, path, hot),
                Laws.scan_quiet(kids, self, ws, lead, path, False{}), Laws.scan_quiet(body, self, ws, lead, path,
                    Bool.and(hot, Calls.calls(body, self))), Laws.scan_quiet(rest, self, ws, lead, path, hot))
            case Tree.SFor{}:
              scan.nil3(Scan.walk(kids, self, ws, [], lead, path, hot), Scan.walk(body, self, ws, [], lead, path, hot),
                  Scan.walk(rest, self, ws, [], lead, path, hot),
                Laws.scan_quiet(kids, self, ws, lead, path, hot), Laws.scan_quiet(body, self, ws, lead, path,
                    hot), Laws.scan_quiet(rest, self, ws, lead, path, hot))
            case Tree.SLet{}:
              scan.nil3(Scan.walk(kids, self, ws, [], lead, path, hot), Scan.walk(body, self, ws, [], lead, path, hot),
                  Scan.walk(rest, self, ws, [], lead, path, hot),
                Laws.scan_quiet(kids, self, ws, lead, path, hot), Laws.scan_quiet(body, self, ws, lead, path,
                    hot), Laws.scan_quiet(rest, self, ws, lead, path, hot))
            case Tree.STerm{}:
              scan.nil3(Scan.walk(kids, self, ws, [], lead, path, hot), Scan.walk(body, self, ws, [], lead, path, hot),
                  Scan.walk(rest, self, ws, [], lead, path, hot),
                Laws.scan_quiet(kids, self, ws, lead, path, hot), Laws.scan_quiet(body, self, ws, lead, path,
                    hot), Laws.scan_quiet(rest, self, ws, lead, path, hot))
        case Tree.NNil{}:
          Laws.scan_quiet(rest, self, ws, lead, path, hot)
        case Tree.NCons{nh, nt}:
          Laws.scan_quiet(rest, self, ws, lead, path, hot)

# whether an answer has a name
def scan.some(mm: Maybe<&2, String>) -> Bool:
  match mm:
    case None{}:
      False{}
    case Some{nm}:
      True{}

# a finding exactly when there is a name
law scan.cite_len:
  for mm: Maybe<&2, String>
  for +tt: String
  for +line: U32
  for +col: U32
  for +self: String
  for +lead: String
  for +path: String
  {List.length(&2, F.Finding, Scan.cite(mm, tt, line, col, self, lead, path)) == Bool.pick(Nat, scan.some(mm), 1n, 0n)
    : Nat}

def scan.cite_len(mm, _tt, _line, _col, _self, _lead, _path):
  match mm:
    case None{}:
      {==}
    case Some{nm}:
      {==}

# the first of two answers has a name when either has
law scan.first_some:
  for aa: Maybe<&2, String>
  for bb: Maybe<&2, String>
  {scan.some(Scan.first(aa, bb)) == Bool.or(scan.some(aa), scan.some(bb)) : Bool}

def scan.first_some(aa, _bb):
  match aa:
    case None{}:
      {==}
    case Some{nm}:
      {==}

# a kept name is there exactly when the list holds it
law scan.pick_some:
  for b: Bool
  for +nm: String
  {scan.some(Bool.pick(Maybe<&2, String>, b, Some{nm}, None{})) == b : Bool}

def scan.pick_some(b, _nm):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# a token kept against the names is the law's named token
law scan.named:
  for tok: Lex.Tok
  for +carried: List<&2, String>
  {scan.some(Scan.keep_in(Scan.name_tok(tok), carried)) == Laws.scan.named(tok, carried) : Bool}

def scan.named(tok, carried):
  match tok:
    case Lex.Tok{k, +t, l, c}:
      match k:
        case Lex.TName{}:
          scan.pick_some(List.contains(~String, ~String.eq, carried, t), t)
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

# an argument kept against the names is the law's lone name
law scan.lone:
  for nn: Tree.Node
  for +carried: List<&2, String>
  {scan.some(Scan.keep_in(Scan.name_of(nn), carried)) == Laws.scan.lone(nn, carried) : Bool}

def scan.lone(nn, carried):
  match nn:
    case Tree.NCons{h, r}:
      match h:
        case Tree.Leaf{tok}:
          match r:
            case Tree.NNil{}:
              scan.named(tok, carried)
            case Tree.Leaf{x}:
              {==}
            case Tree.Group{x, y, z}:
              {==}
            case Tree.Stmt{x, y, z}:
              {==}
            case Tree.NCons{x, y}:
              {==}
        case Tree.Group{x, y, z}:
          {==}
        case Tree.Stmt{x, y, z}:
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

# a found step's two sides are the law's
law scan.found.or:
  for +arg: Tree.Node
  for rest: List<&2, Nat>
  for +as: List<&2, Tree.Node>
  for +carried: List<&2, String>
  for ih: {scan.some(Scan.found(rest, as, carried)) == Laws.scan.held(rest, as, carried) : Bool}
  {Bool.or(scan.some(Scan.keep_in(Scan.name_of(arg), carried)), scan.some(Scan.found(rest, as, carried)))
    == Bool.or(Laws.scan.lone(arg, carried), Laws.scan.held(rest, as, carried)) : Bool}

def scan.found.or(arg, rest, as, carried, ih):
  %scan.lone(arg, carried) : {Bool.or(scan.some(Scan.keep_in(Scan.name_of(arg), carried)),
    scan.some(Scan.found(rest, as, carried))) == Bool.or(_, Laws.scan.held(rest, as, carried)) : Bool}
  %ih : {Bool.or(scan.some(Scan.keep_in(Scan.name_of(arg), carried)),
    scan.some(Scan.found(rest, as, carried))) == Bool.or(scan.some(Scan.keep_in(Scan.name_of(arg), carried)), _)
      : Bool}
  {==}

# a walked argument is found exactly when the law's held says so
law scan.found:
  for ss: List<&2, Nat>
  for +as: List<&2, Tree.Node>
  for +carried: List<&2, String>
  {scan.some(Scan.found(ss, as, carried)) == Laws.scan.held(ss, as, carried) : Bool}

def scan.found(ss, as, carried):
  match ss:
    case Nil{}:
      {==}
    case Con{+at, +rest}:
      +arg = Calls.arg(as, at)
      +lh = Laws.scan.lone(arg, carried)
      Equal.trans(Bool, scan.some(Scan.first(Scan.keep_in(Scan.name_of(arg), carried), Scan.found(rest, as, carried))),
        Bool.or(scan.some(Scan.keep_in(Scan.name_of(arg), carried)), scan.some(Scan.found(rest, as, carried))),
        Bool.or(lh, Laws.scan.held(rest, as, carried)),
        scan.first_some(Scan.keep_in(Scan.name_of(arg), carried), Scan.found(rest, as, carried)),
        scan.found.or(arg, rest, as, carried, scan.found(rest, as, carried)))

# a gated finding list counts when the gate opens and it counts
law scan.gate_len:
  for hot: Bool
  for open: Bool
  for q: Bool
  for -x: List<&2, F.Finding>
  for -hb: Bool
  for ex: {List.length(&2, F.Finding, x) == Bool.pick(Nat, hb, 1n, 0n) : Nat}
  {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, Bool.not(Bool.and(hot, Bool.and(open, Bool.not(q)))), [],
    _u => x)) == Bool.pick(Nat, Bool.and(hot, Bool.and(open, Bool.and(Bool.not(q), hb))), 1n, 0n) : Nat}

def scan.gate_len(hot, open, q, _x, _hb, ex):
  match hot:
    case False{}:
      {==}
    case True{}:
      match open:
        case False{}:
          {==}
        case True{}:
          match q:
            case True{}:
              {==}
            case False{}:
              ex

# a named call's finding count is the law's
law scan.on_len:
  for +hot: Bool
  for +open: Bool
  for +tt: String
  for +line: U32
  for +col: U32
  for +kids: Tree.Node
  for +self: String
  for +ws: List<&2, Scan.Walk>
  for +carried: List<&2, String>
  for +lead: String
  for +path: String
  {List.length(&2, F.Finding, Scan.on_name(hot, open, tt, line, col, kids, self, ws, carried, lead, path))
    == Bool.pick(Nat, Bool.and(hot, Bool.and(open, Bool.and(Bool.not(String.eq(tt, self)),
      Laws.scan.held(Scan.slots(tt, ws), Calls.args(kids), carried)))), 1n, 0n) : Nat}

def scan.on_len(hot, open, tt, line, col, kids, self, ws, carried, lead, path):
  +fd = Scan.found(Scan.slots(tt, ws), Calls.args(kids), carried)
  +hb = Laws.scan.held(Scan.slots(tt, ws), Calls.args(kids), carried)
  scan.gate_len(hot, open, String.eq(tt, self), Scan.cite(fd, tt, line, col, self, lead, path), hb,
    Equal.trans(Nat, List.length(&2, F.Finding, Scan.cite(fd, tt, line, col, self, lead, path)),
      Bool.pick(Nat, scan.some(fd), 1n, 0n), Bool.pick(Nat, hb, 1n, 0n),
      scan.cite_len(fd, tt, line, col, self, lead, path),
      Equal.cong(Bool, Nat, b => Bool.pick(Nat, b, 1n, 0n), scan.some(fd), hb,
        scan.found(Scan.slots(tt, ws), Calls.args(kids), carried))))

# a call's finding count is the law's, whatever its callee's kind
law scan.hit_len:
  for kk: Lex.TokKind
  for +hot: Bool
  for +open: Bool
  for +tt: String
  for +line: U32
  for +col: U32
  for +kids: Tree.Node
  for +self: String
  for +ws: List<&2, Scan.Walk>
  for +carried: List<&2, String>
  for +lead: String
  for +path: String
  {List.length(&2, F.Finding, Scan.call_hit(kk, hot, open, tt, line, col, kids, self, ws, carried, lead, path))
    == Bool.pick(Nat, Laws.scan.call(kk, hot, open, tt, kids, self, ws, carried), 1n, 0n) : Nat}

def scan.hit_len(kk, hot, open, tt, line, col, kids, self, ws, carried, lead, path):
  match kk:
    case Lex.TName{}:
      scan.on_len(hot, open, tt, line, col, kids, self, ws, carried, lead, path)
    case Lex.TUpper{}:
      {==}
    case Lex.TDotted{}:
      scan.on_len(hot, open, tt, line, col, kids, self, ws, carried, lead, path)
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

# scan's walk counts the calls the law counts, at every heat
law scan.walk:
  for nn: Tree.Node
  for +self: String
  for +ws: List<&2, Scan.Walk>
  for +carried: List<&2, String>
  for +lead: String
  for +path: String
  for +hot: Bool
  {List.length(&2, F.Finding, Scan.walk(nn, self, ws, carried, lead, path, hot))
    == Laws.scan.count(nn, self, ws, carried, hot) : Nat}

def scan.walk(nn, self, ws, carried, lead, path, hot):
  match nn:
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
        case Tree.Leaf{Lex.Tok{+k, +t, +l, +c}}:
          match rest:
            case Tree.Leaf{tok}:
              {==}
            case Tree.Group{o, gk, cl}:
              {==}
            case Tree.Stmt{kind, sk, sb}:
              {==}
            case Tree.NNil{}:
              {==}
            case Tree.NCons{rh, +rr}:
              match rh:
                case Tree.Group{Lex.Tok{gk, +o, gl, gc}, +kids, cl}:
                  M1.chars.sum(Scan.call_hit(k, Hoist.warm(hot, k), String.eq(o, "("), t, l, c, kids, self, ws, carried,
                      lead, path),
                    Scan.walk(kids, self, ws, carried, lead, path, Hoist.warm(hot, k)),
                    Scan.walk(rr, self, ws, carried, lead, path, Hoist.warm(hot, k)),
                    Bool.pick(Nat, Laws.scan.call(k, Hoist.warm(hot, k), String.eq(o, "("), t, kids, self, ws,
                        carried), 1n, 0n),
                    Laws.scan.count(kids, self, ws, carried, Hoist.warm(hot, k)), Laws.scan.count(rr, self, ws,
                        carried, Hoist.warm(hot, k)),
                    scan.hit_len(k, Hoist.warm(hot, k), String.eq(o, "("), t, l, c, kids, self, ws, carried, lead,
                        path),
                    scan.walk(kids, self, ws, carried, lead, path, Hoist.warm(hot, k)),
                    scan.walk(rr, self, ws, carried, lead, path, Hoist.warm(hot, k)))
                case Tree.Leaf{tok}:
                  scan.walk(rest, self, ws, carried, lead, path, Hoist.warm(hot, k))
                case Tree.Stmt{kind, sk, sb}:
                  scan.walk(rest, self, ws, carried, lead, path, Hoist.warm(hot, k))
                case Tree.NNil{}:
                  scan.walk(rest, self, ws, carried, lead, path, Hoist.warm(hot, k))
                case Tree.NCons{nh, nt}:
                  scan.walk(rest, self, ws, carried, lead, path, Hoist.warm(hot, k))
        case Tree.Group{o, +kids, cl}:
          M1.index.two(Scan.walk(kids, self, ws, carried, lead, path, hot), Scan.walk(rest, self, ws, carried, lead,
              path,
              hot),
            Laws.scan.count(kids, self, ws, carried, hot), Laws.scan.count(rest, self, ws, carried, hot),
            scan.walk(kids, self, ws, carried, lead, path, hot), scan.walk(rest, self, ws, carried, lead, path, hot))
        case Tree.Stmt{kind, +kids, +body}:
          match kind:
            case Tree.SDef{}:
              M1.chars.sum(Scan.walk(kids, self, ws, carried, lead, path, hot), Scan.walk(body, self, ws, carried, lead,
                  path, hot),
                Scan.walk(rest, self, ws, carried, lead, path, hot), Laws.scan.count(kids, self, ws, carried, hot),
                Laws.scan.count(body, self, ws, carried, hot), Laws.scan.count(rest, self, ws, carried, hot),
                scan.walk(kids, self, ws, carried, lead, path, hot), scan.walk(body, self, ws, carried, lead, path,
                    hot),
                scan.walk(rest, self, ws, carried, lead, path, hot))
            case Tree.SType{}:
              M1.chars.sum(Scan.walk(kids, self, ws, carried, lead, path, hot), Scan.walk(body, self, ws, carried, lead,
                  path, hot),
                Scan.walk(rest, self, ws, carried, lead, path, hot), Laws.scan.count(kids, self, ws, carried, hot),
                Laws.scan.count(body, self, ws, carried, hot), Laws.scan.count(rest, self, ws, carried, hot),
                scan.walk(kids, self, ws, carried, lead, path, hot), scan.walk(body, self, ws, carried, lead, path,
                    hot),
                scan.walk(rest, self, ws, carried, lead, path, hot))
            case Tree.SLaw{}:
              M1.chars.sum(Scan.walk(kids, self, ws, carried, lead, path, hot), Scan.walk(body, self, ws, carried, lead,
                  path, hot),
                Scan.walk(rest, self, ws, carried, lead, path, hot), Laws.scan.count(kids, self, ws, carried, hot),
                Laws.scan.count(body, self, ws, carried, hot), Laws.scan.count(rest, self, ws, carried, hot),
                scan.walk(kids, self, ws, carried, lead, path, hot), scan.walk(body, self, ws, carried, lead, path,
                    hot),
                scan.walk(rest, self, ws, carried, lead, path, hot))
            case Tree.SImport{}:
              M1.chars.sum(Scan.walk(kids, self, ws, carried, lead, path, hot), Scan.walk(body, self, ws, carried, lead,
                  path, hot),
                Scan.walk(rest, self, ws, carried, lead, path, hot), Laws.scan.count(kids, self, ws, carried, hot),
                Laws.scan.count(body, self, ws, carried, hot), Laws.scan.count(rest, self, ws, carried, hot),
                scan.walk(kids, self, ws, carried, lead, path, hot), scan.walk(body, self, ws, carried, lead, path,
                    hot),
                scan.walk(rest, self, ws, carried, lead, path, hot))
            case Tree.SCase{}:
              M1.chars.sum(Scan.walk(kids, self, ws, carried, lead, path, False{}), Scan.walk(body, self, ws, carried,
                  lead, path, Bool.and(hot, Calls.calls(body, self))),
                Scan.walk(rest, self, ws, carried, lead, path, hot), Laws.scan.count(kids, self, ws, carried, False{}),
                Laws.scan.count(body, self, ws, carried, Bool.and(hot, Calls.calls(body, self))), Laws.scan.count(rest,
                    self, ws, carried, hot),
                scan.walk(kids, self, ws, carried, lead, path, False{}), scan.walk(body, self, ws, carried, lead, path,
                    Bool.and(hot, Calls.calls(body, self))),
                scan.walk(rest, self, ws, carried, lead, path, hot))
            case Tree.SFor{}:
              M1.chars.sum(Scan.walk(kids, self, ws, carried, lead, path, hot), Scan.walk(body, self, ws, carried, lead,
                  path, hot),
                Scan.walk(rest, self, ws, carried, lead, path, hot), Laws.scan.count(kids, self, ws, carried, hot),
                Laws.scan.count(body, self, ws, carried, hot), Laws.scan.count(rest, self, ws, carried, hot),
                scan.walk(kids, self, ws, carried, lead, path, hot), scan.walk(body, self, ws, carried, lead, path,
                    hot),
                scan.walk(rest, self, ws, carried, lead, path, hot))
            case Tree.SLet{}:
              M1.chars.sum(Scan.walk(kids, self, ws, carried, lead, path, hot), Scan.walk(body, self, ws, carried, lead,
                  path, hot),
                Scan.walk(rest, self, ws, carried, lead, path, hot), Laws.scan.count(kids, self, ws, carried, hot),
                Laws.scan.count(body, self, ws, carried, hot), Laws.scan.count(rest, self, ws, carried, hot),
                scan.walk(kids, self, ws, carried, lead, path, hot), scan.walk(body, self, ws, carried, lead, path,
                    hot),
                scan.walk(rest, self, ws, carried, lead, path, hot))
            case Tree.STerm{}:
              M1.chars.sum(Scan.walk(kids, self, ws, carried, lead, path, hot), Scan.walk(body, self, ws, carried, lead,
                  path, hot),
                Scan.walk(rest, self, ws, carried, lead, path, hot), Laws.scan.count(kids, self, ws, carried, hot),
                Laws.scan.count(body, self, ws, carried, hot), Laws.scan.count(rest, self, ws, carried, hot),
                scan.walk(kids, self, ws, carried, lead, path, hot), scan.walk(body, self, ws, carried, lead, path,
                    hot),
                scan.walk(rest, self, ws, carried, lead, path, hot))
        case Tree.NNil{}:
          scan.walk(rest, self, ws, carried, lead, path, hot)
        case Tree.NCons{nh, nt}:
          scan.walk(rest, self, ws, carried, lead, path, hot)

# a def that calls itself and is not a proof gathers its walk, entered hot,
# any other nothing
law scan.def:
  for g: Bool
  for +sig: Tree.Node
  for +body: Tree.Node
  for +name: String
  for +ws: List<&2, Scan.Walk>
  for +path: String
  {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, Bool.not(g), [], _u => Scan.run(sig, body, name, ws,
      path)))
    == Bool.pick(Nat, g, Laws.scan.count(body, name, ws, Hoist.carried(sig, body, name), True{}), 0n) : Nat}

def scan.def(g, sig, body, name, ws, path):
  match g:
    case True{}:
      +carried = Hoist.carried(sig, body, name)
      scan.walk(body, name, ws, carried, Scan.lead.go(Calls.params(sig), carried), path, True{})
    case False{}:
      {==}

# over the defs, the rule's join counts what it gathered and what the law
# counts
law scan.go:
  for ds: List<&2, Calls.Def>
  for +ws: List<&2, Scan.Walk>
  for +path: String
  for +acc: List<&2, List<&2, F.Finding>>
  {List.length(&2, F.Finding, Scan.check.go(ds, ws, path, acc))
    == Nat.add(M1.index.sum(acc), Laws.scan.total(ds, ws, path)) : Nat}

def scan.go(ds, ws, path, acc):
  match ds:
    case Nil{}:
      M1.index.flat(acc, Nil{})
    case Con{Calls.Def{+name, +sig, +body}, +rest}:
      +g = Bool.and(Calls.calls(body, name), Bool.not(Calls.exempt(path, sig)))
      +x = Lazy.stop(List<&2, F.Finding>, Bool.not(g), [], _u => Scan.run(sig, body, name, ws, path))
      +n = Bool.pick(Nat, g, Laws.scan.count(body, name, ws, Hoist.carried(sig, body, name), True{}), 0n)
      +tot = Laws.scan.total(rest, ws, path)
      Equal.trans(Nat,
        List.length(&2, F.Finding, Scan.check.go(rest, ws, path, x <> acc)),
        Nat.add(Nat.add(M1.index.sum(acc), List.length(&2, F.Finding, x)), tot),
        Nat.add(M1.index.sum(acc), Nat.add(n, tot)),
        scan.go(rest, ws, path, x <> acc),
        Equal.trans(Nat,
          Nat.add(Nat.add(M1.index.sum(acc), List.length(&2, F.Finding, x)), tot),
          Nat.add(M1.index.sum(acc), Nat.add(List.length(&2, F.Finding, x), tot)),
          Nat.add(M1.index.sum(acc), Nat.add(n, tot)),
          M1.index.assoc(M1.index.sum(acc), List.length(&2, F.Finding, x), tot),
          Equal.cong(Nat, Nat, z => Nat.add(M1.index.sum(acc), Nat.add(z, tot)), List.length(&2, F.Finding, x), n,
            scan.def(g, sig, body, name, ws, path))))

def Laws.scan_counts(path, _text, _toks, tree, _bound, _items, e):
  +ds = Calls.defs(tree)
  %Equal.sym(Bool, Paths.is_law_file(path), False{}, e) : {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>,
    _, [], _u => Scan.check.on(ds, path))) == Laws.scan.total(ds, Scan.walks(ds), path) : Nat}
  scan.go(ds, Scan.walks(ds), path, Nil{})
