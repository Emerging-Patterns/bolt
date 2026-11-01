# proofs of laws/UnitReportsMultiplyByOne.bend
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/lazy/lazy.bend as Lazy
import ../src/syntax/tree.bend as Tree
import ../src/rules/calls.bend as Calls
import ../src/rules/correctness/pick.bend as Pick
import ../src/rules/suspicious/unit.bend as UnitRule
import ../laws/UnitReportsMultiplyByOne.bend as Laws
import ./lemmas/Pick.bend as M1

# unit (laws/UnitReportsMultiplyByOne.bend): the rule's literal, operator and call tests are the
# law's, read through whether a maybe holds a token (unit.has), and its walk
# counts the law's count.

# does the maybe hold a token?
def unit.has(mm: Maybe<&2, Lex.Tok>) -> Bool:
  match mm:
    case None{}:
      False{}
    case Some{tok}:
      True{}

# a finding on the maybe's token: one when it holds one
law unit.cite:
  for mm: Maybe<&2, Lex.Tok>
  for +path: String
  {List.length(&2, F.Finding, UnitRule.cite(mm, path)) == Bool.pick(Nat, unit.has(mm), 1n, 0n) : Nat}

def unit.cite(mm, _path):
  match mm:
    case None{}:
      {==}
    case Some{tok}:
      match tok:
        case Lex.Tok{k, t, l, c}:
          {==}

# a pick between a token and none holds one exactly when it picks the token
law unit.hp:
  for b: Bool
  for -tok: Lex.Tok
  {unit.has(Bool.pick(Maybe<&2, Lex.Tok>, b, Some{tok}, None{})) == b : Bool}

def unit.hp(b, _tok):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the rule's literal one is the law's
law unit.one_is:
  for mm: Maybe<&2, Lex.Tok>
  {unit.has(UnitRule.one_of(mm)) == Laws.unit.one(mm) : Bool}

def unit.one_is(mm):
  match mm:
    case None{}:
      {==}
    case Some{tok}:
      match tok:
        case Lex.Tok{k, +t, l, c}:
          match k:
            case Lex.TName{}:
              {==}
            case Lex.TUpper{}:
              {==}
            case Lex.TDotted{}:
              {==}
            case Lex.TWild{}:
              {==}
            case Lex.TKey{}:
              {==}
            case Lex.TNum{}:
              unit.hp(UnitRule.one_text(t), Lex.Tok{Lex.TNum{}, t, l, c})
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

# the first of two maybes that holds a token: one when either holds one
law unit.either:
  for xx: Maybe<&2, Lex.Tok>
  for -yy: Maybe<&2, Lex.Tok>
  {unit.has(UnitRule.either(xx, yy)) == Bool.or(unit.has(xx), unit.has(yy)) : Bool}

def unit.either(xx, _yy):
  match xx:
    case None{}:
      {==}
    case Some{tok}:
      {==}

# equal Bools give equal ors
law unit.or2:
  for -a: Bool
  for -b: Bool
  for -c: Bool
  for -d: Bool
  for e1: {a == b : Bool}
  for e2: {c == d : Bool}
  {Bool.or(a, c) == Bool.or(b, d) : Bool}

def unit.or2(a, b, c, d, e1, e2):
  Equal.trans(Bool, Bool.or(a, c), Bool.or(b, c), Bool.or(b, d), Equal.cong(Bool, Bool, x => Bool.or(x, c), a, b, e1),
    Equal.cong(Bool, Bool, x => Bool.or(b, x), c, d, e2))

# or commutes
law unit.comm:
  for a: Bool
  for b: Bool
  {Bool.or(a, b) == Bool.or(b, a) : Bool}

def unit.comm(a, b):
  match a:
    case True{}:
      match b:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      match b:
        case True{}:
          {==}
        case False{}:
          {==}

# the literal an operator's finding cites is there exactly when the law's
# operator is by one: `*` (s) with one after or before, `/` (d) with one after
law unit.which:
  for s: Bool
  for d: Bool
  for +pp: Maybe<&2, Lex.Tok>
  for +nn: Maybe<&2, Lex.Tok>
  {unit.has(Bool.pick(Maybe<&2, Lex.Tok>, s, UnitRule.either(UnitRule.one_of(nn), UnitRule.one_of(pp)),
    Bool.pick(Maybe<&2, Lex.Tok>, d, UnitRule.one_of(nn), None{})))
    == Bool.pick(Bool, s, Bool.or(Laws.unit.one(nn), Laws.unit.one(pp)), Bool.and(d, Laws.unit.one(nn))) : Bool}

def unit.which(s, d, pp, nn):
  match s:
    case True{}:
      Equal.trans(Bool, unit.has(UnitRule.either(UnitRule.one_of(nn), UnitRule.one_of(pp))),
        Bool.or(unit.has(UnitRule.one_of(nn)), unit.has(UnitRule.one_of(pp))),
        Bool.or(Laws.unit.one(nn), Laws.unit.one(pp)),
        unit.either(UnitRule.one_of(nn), UnitRule.one_of(pp)),
        unit.or2(unit.has(UnitRule.one_of(nn)), Laws.unit.one(nn), unit.has(UnitRule.one_of(pp)), Laws.unit.one(pp),
          unit.one_is(nn), unit.one_is(pp)))
    case False{}:
      match d:
        case True{}:
          unit.one_is(nn)
        case False{}:
          {==}

# the node after, to the rule and to the law
law unit.first_is:
  for nn: Tree.Node
  {UnitRule.first_tok(nn) == Laws.unit.first(nn) : Maybe<&2, Lex.Tok>}

def unit.first_is(nn):
  match nn:
    case Tree.NCons{h, r}:
      match h:
        case Tree.Leaf{tok}:
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

# an operator's finding: one exactly when it is by one
law unit.opx:
  for +t: String
  for +prev: Maybe<&2, Lex.Tok>
  for +rest: Tree.Node
  for +path: String
  {List.length(&2, F.Finding, UnitRule.cite(UnitRule.which(t, prev, UnitRule.first_tok(rest)), path))
    == Bool.pick(Nat, Laws.unit.by_one(t, prev, Laws.unit.first(rest)), 1n, 0n) : Nat}

def unit.opx(t, prev, rest, path):
  +ft = UnitRule.first_tok(rest)
  +uf = Laws.unit.first(rest)
  +wh = UnitRule.which(t, prev, ft)
  Equal.trans(Nat, List.length(&2, F.Finding, UnitRule.cite(wh, path)), Bool.pick(Nat, unit.has(wh), 1n, 0n),
    Bool.pick(Nat, Laws.unit.by_one(t, prev, uf), 1n, 0n), unit.cite(wh, path),
    Equal.cong(Bool, Nat, b => Bool.pick(Nat, b, 1n, 0n), unit.has(wh), Laws.unit.by_one(t, prev, uf),
      Equal.trans(Bool, unit.has(wh), Laws.unit.by_one(t, prev, ft), Laws.unit.by_one(t, prev, uf),
        unit.which(String.eq(t, "*"), String.eq(t, "/"), prev, ft),
        Equal.cong(Maybe<&2, Lex.Tok>, Bool, m => Laws.unit.by_one(t, prev, m), ft, uf, unit.first_is(rest)))))

# an operator in a region as hot as hot: its finding when hot
law unit.on:
  for hot: Bool
  for -x: List<&2, F.Finding>
  for -b: Bool
  for e: {List.length(&2, F.Finding, x) == Bool.pick(Nat, b, 1n, 0n) : Nat}
  {List.length(&2, F.Finding, Bool.pick(List<&2, F.Finding>, Bool.and(hot, True{}), x, []))
    == Bool.pick(Nat, Bool.and(hot, b), 1n, 0n) : Nat}

def unit.on(hot, _x, _b, e):
  match hot:
    case True{}:
      e
    case False{}:
      {==}

# a leaf that is no operator: no finding
law unit.off:
  for hot: Bool
  for -x: List<&2, F.Finding>
  {List.length(&2, F.Finding, Bool.pick(List<&2, F.Finding>, Bool.and(hot, False{}), x, []))
    == Bool.pick(Nat, Bool.and(hot, False{}), 1n, 0n) : Nat}

def unit.off(hot, _x):
  match hot:
    case True{}:
      {==}
    case False{}:
      {==}

# a leaf's own finding onto the rest's
law unit.leaf:
  for +x: List<&2, F.Finding>
  for +more: List<&2, F.Finding>
  for +b: Bool
  for -m: Nat
  for ex: {List.length(&2, F.Finding, x) == Bool.pick(Nat, b, 1n, 0n) : Nat}
  for em: {List.length(&2, F.Finding, more) == m : Nat}
  {List.length(&2, F.Finding, List.append(&2, F.Finding, x, more)) == Bool.pick(Nat, b, 1n+m, m) : Nat}

def unit.leaf(x, more, b, m, ex, em):
  Equal.trans(Nat, List.length(&2, F.Finding, List.append(&2, F.Finding, x, more)), Nat.add(Bool.pick(Nat, b, 1n, 0n),
    m),
    Bool.pick(Nat, b, 1n+m, m), M1.pick.join(x, more, Bool.pick(Nat, b, 1n, 0n), m, ex, em), M1.fuel.addpick(b, m))

# the rule's argument that is the literal one alone is the law's
law unit.arg_is:
  for aa: Tree.Node
  {unit.has(UnitRule.arg_one(aa)) == Laws.unit.lone(aa) : Bool}

def unit.arg_is(aa):
  match aa:
    case Tree.NCons{h, r}:
      match h:
        case Tree.Leaf{tok}:
          match r:
            case Tree.NNil{}:
              unit.one_is(Some{tok})
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

# the rule's some argument one is the law's
law unit.any_is:
  for as: List<&2, Tree.Node>
  {unit.has(UnitRule.any_one(as)) == Laws.unit.any(as) : Bool}

def unit.any_is(as):
  match as:
    case Nil{}:
      {==}
    case Con{+h, +rest}:
      Equal.trans(Bool, unit.has(UnitRule.either(UnitRule.any_one(rest), UnitRule.arg_one(h))),
        Bool.or(unit.has(UnitRule.any_one(rest)), unit.has(UnitRule.arg_one(h))),
        Bool.or(Laws.unit.lone(h), Laws.unit.any(rest)),
        unit.either(UnitRule.any_one(rest), UnitRule.arg_one(h)),
        Equal.trans(Bool, Bool.or(unit.has(UnitRule.any_one(rest)), unit.has(UnitRule.arg_one(h))),
          Bool.or(Laws.unit.any(rest), Laws.unit.lone(h)), Bool.or(Laws.unit.lone(h), Laws.unit.any(rest)),
          unit.or2(unit.has(UnitRule.any_one(rest)), Laws.unit.any(rest), unit.has(UnitRule.arg_one(h)),
            Laws.unit.lone(h), unit.any_is(rest), unit.arg_is(h)),
          unit.comm(Laws.unit.any(rest), Laws.unit.lone(h))))

# the rule's last argument one is the law's
law unit.last_is:
  for as: List<&2, Tree.Node>
  {unit.has(UnitRule.last_one(as)) == Laws.unit.last(as) : Bool}

def unit.last_is(as):
  match as:
    case Nil{}:
      {==}
    case Con{h, t}:
      match t:
        case Nil{}:
          unit.arg_is(h)
        case Con{x, y}:
          unit.last_is(t)

# a finding on what the maybe holds, as the law's Bool says
law unit.has_is:
  for +mm: Maybe<&2, Lex.Tok>
  for -b: Bool
  for +path: String
  for e: {unit.has(mm) == b : Bool}
  {List.length(&2, F.Finding, UnitRule.cite(mm, path)) == Bool.pick(Nat, b, 1n, 0n) : Nat}

def unit.has_is(mm, b, path, e):
  Equal.trans(Nat, List.length(&2, F.Finding, UnitRule.cite(mm, path)), Bool.pick(Nat, unit.has(mm), 1n, 0n),
    Bool.pick(Nat, b, 1n, 0n), unit.cite(mm, path), Equal.cong(Bool, Nat, x => Bool.pick(Nat, x, 1n, 0n), unit.has(mm),
      b, e))

# a divide's finding, when the call is a divide
law unit.div:
  for db: Bool
  for +as: List<&2, Tree.Node>
  for +path: String
  {List.length(&2, F.Finding, UnitRule.on_div_is(db, as, path)) == Bool.pick(Nat, Bool.and(db, Laws.unit.last(as)), 1n,
    0n)
    : Nat}

def unit.div(db, as, path):
  match db:
    case True{}:
      unit.has_is(UnitRule.last_one(as), Laws.unit.last(as), path, unit.last_is(as))
    case False{}:
      {==}

# a multiply's finding, else a divide's
law unit.opis:
  for mb: Bool
  for +tt: String
  for +as: List<&2, Tree.Node>
  for +path: String
  {List.length(&2, F.Finding, UnitRule.on_op_is(mb, tt, as, path))
    == Bool.pick(Nat, Bool.pick(Bool, mb, Laws.unit.any(as),
      Bool.and(List.contains(~String, ~String.eq, ["Nat.div", "U32.div", "F32.div"], tt),
        Laws.unit.last(as))), 1n, 0n)
    : Nat}

def unit.opis(mb, tt, as, path):
  match mb:
    case True{}:
      unit.has_is(UnitRule.any_one(as), Laws.unit.any(as), path, unit.any_is(as))
    case False{}:
      unit.div(List.contains(~String, ~String.eq, ["Nat.div", "U32.div", "F32.div"], tt), as, path)

# a group's own finding: a `(` call that multiplies or divides by one, when hot
law unit.own:
  for call: Bool
  for +tt: String
  for +kids: Tree.Node
  for +path: String
  for hot: Bool
  {List.length(&2, F.Finding, UnitRule.own_of(call, tt, kids, path, hot))
    == Bool.pick(Nat, Bool.and(call, Bool.and(hot, Laws.unit.call(tt, Calls.args(kids)))), 1n, 0n) : Nat}

def unit.own(call, tt, kids, path, hot):
  match call:
    case True{}:
      match hot:
        case True{}:
          unit.opis(List.contains(~String, ~String.eq, ["Nat.mul", "U32.mul", "F32.mul"], tt), tt,
            Calls.args(kids), path)
        case False{}:
          {==}
    case False{}:
      {==}

# the name a group calls, to the rule and to the law
law unit.callee:
  for mm: Maybe<&2, Lex.Tok>
  {UnitRule.callee(mm) == Laws.unit.name(mm) : String}

def unit.callee(mm):
  match mm:
    case None{}:
      {==}
    case Some{tok}:
      match tok:
        case Lex.Tok{k, t, l, c}:
          {==}

def Laws.unit_walk_counts(nn, prev, self, path, hot):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{k, +t, +l, +c}:
              match k:
                case Lex.TName{}:
                  unit.leaf(UnitRule.op_hit(Lex.Tok{Lex.TName{}, t, l, c}, prev, UnitRule.first_tok(rest), path, hot),
                    UnitRule.walk(rest, Some{Lex.Tok{Lex.TName{}, t, l, c}}, self, path, hot),
                    Bool.and(hot, False{}), Laws.unit.count(rest, Some{Lex.Tok{Lex.TName{}, t, l, c}}, self, hot),
                    unit.off(hot, UnitRule.cite(UnitRule.which(t, prev, UnitRule.first_tok(rest)), path)),
                    Laws.unit_walk_counts(rest, Some{Lex.Tok{Lex.TName{}, t, l, c}}, self, path, hot))
                case Lex.TUpper{}:
                  unit.leaf(UnitRule.op_hit(Lex.Tok{Lex.TUpper{}, t, l, c}, prev, UnitRule.first_tok(rest), path, hot),
                    UnitRule.walk(rest, Some{Lex.Tok{Lex.TUpper{}, t, l, c}}, self, path, hot),
                    Bool.and(hot, False{}), Laws.unit.count(rest, Some{Lex.Tok{Lex.TUpper{}, t, l, c}}, self, hot),
                    unit.off(hot, UnitRule.cite(UnitRule.which(t, prev, UnitRule.first_tok(rest)), path)),
                    Laws.unit_walk_counts(rest, Some{Lex.Tok{Lex.TUpper{}, t, l, c}}, self, path, hot))
                case Lex.TDotted{}:
                  unit.leaf(UnitRule.op_hit(Lex.Tok{Lex.TDotted{}, t, l, c}, prev, UnitRule.first_tok(rest), path, hot),
                    UnitRule.walk(rest, Some{Lex.Tok{Lex.TDotted{}, t, l, c}}, self, path, hot),
                    Bool.and(hot, False{}), Laws.unit.count(rest, Some{Lex.Tok{Lex.TDotted{}, t, l, c}}, self, hot),
                    unit.off(hot, UnitRule.cite(UnitRule.which(t, prev, UnitRule.first_tok(rest)), path)),
                    Laws.unit_walk_counts(rest, Some{Lex.Tok{Lex.TDotted{}, t, l, c}}, self, path, hot))
                case Lex.TWild{}:
                  unit.leaf(UnitRule.op_hit(Lex.Tok{Lex.TWild{}, t, l, c}, prev, UnitRule.first_tok(rest), path, hot),
                    UnitRule.walk(rest, Some{Lex.Tok{Lex.TWild{}, t, l, c}}, self, path, hot),
                    Bool.and(hot, False{}), Laws.unit.count(rest, Some{Lex.Tok{Lex.TWild{}, t, l, c}}, self, hot),
                    unit.off(hot, UnitRule.cite(UnitRule.which(t, prev, UnitRule.first_tok(rest)), path)),
                    Laws.unit_walk_counts(rest, Some{Lex.Tok{Lex.TWild{}, t, l, c}}, self, path, hot))
                case Lex.TKey{}:
                  unit.leaf(UnitRule.op_hit(Lex.Tok{Lex.TKey{}, t, l, c}, prev, UnitRule.first_tok(rest), path, hot),
                    UnitRule.walk(rest, Some{Lex.Tok{Lex.TKey{}, t, l, c}}, self, path, hot),
                    Bool.and(hot, False{}), Laws.unit.count(rest, Some{Lex.Tok{Lex.TKey{}, t, l, c}}, self, hot),
                    unit.off(hot, UnitRule.cite(UnitRule.which(t, prev, UnitRule.first_tok(rest)), path)),
                    Laws.unit_walk_counts(rest, Some{Lex.Tok{Lex.TKey{}, t, l, c}}, self, path, hot))
                case Lex.TNum{}:
                  unit.leaf(UnitRule.op_hit(Lex.Tok{Lex.TNum{}, t, l, c}, prev, UnitRule.first_tok(rest), path, hot),
                    UnitRule.walk(rest, Some{Lex.Tok{Lex.TNum{}, t, l, c}}, self, path, hot),
                    Bool.and(hot, False{}), Laws.unit.count(rest, Some{Lex.Tok{Lex.TNum{}, t, l, c}}, self, hot),
                    unit.off(hot, UnitRule.cite(UnitRule.which(t, prev, UnitRule.first_tok(rest)), path)),
                    Laws.unit_walk_counts(rest, Some{Lex.Tok{Lex.TNum{}, t, l, c}}, self, path, hot))
                case Lex.TStr{}:
                  unit.leaf(UnitRule.op_hit(Lex.Tok{Lex.TStr{}, t, l, c}, prev, UnitRule.first_tok(rest), path, hot),
                    UnitRule.walk(rest, Some{Lex.Tok{Lex.TStr{}, t, l, c}}, self, path, hot),
                    Bool.and(hot, False{}), Laws.unit.count(rest, Some{Lex.Tok{Lex.TStr{}, t, l, c}}, self, hot),
                    unit.off(hot, UnitRule.cite(UnitRule.which(t, prev, UnitRule.first_tok(rest)), path)),
                    Laws.unit_walk_counts(rest, Some{Lex.Tok{Lex.TStr{}, t, l, c}}, self, path, hot))
                case Lex.TChar{}:
                  unit.leaf(UnitRule.op_hit(Lex.Tok{Lex.TChar{}, t, l, c}, prev, UnitRule.first_tok(rest), path, hot),
                    UnitRule.walk(rest, Some{Lex.Tok{Lex.TChar{}, t, l, c}}, self, path, hot),
                    Bool.and(hot, False{}), Laws.unit.count(rest, Some{Lex.Tok{Lex.TChar{}, t, l, c}}, self, hot),
                    unit.off(hot, UnitRule.cite(UnitRule.which(t, prev, UnitRule.first_tok(rest)), path)),
                    Laws.unit_walk_counts(rest, Some{Lex.Tok{Lex.TChar{}, t, l, c}}, self, path, hot))
                case Lex.TComment{}:
                  unit.leaf(UnitRule.op_hit(Lex.Tok{Lex.TComment{}, t, l, c}, prev, UnitRule.first_tok(rest), path,
                    hot), UnitRule.walk(rest, Some{Lex.Tok{Lex.TComment{}, t, l, c}}, self, path, hot),
                    Bool.and(hot, False{}), Laws.unit.count(rest, Some{Lex.Tok{Lex.TComment{}, t, l, c}}, self, hot),
                    unit.off(hot, UnitRule.cite(UnitRule.which(t, prev, UnitRule.first_tok(rest)), path)),
                    Laws.unit_walk_counts(rest, Some{Lex.Tok{Lex.TComment{}, t, l, c}}, self, path, hot))
                case Lex.TSpace{}:
                  unit.leaf(UnitRule.op_hit(Lex.Tok{Lex.TSpace{}, t, l, c}, prev, UnitRule.first_tok(rest), path, hot),
                    UnitRule.walk(rest, Some{Lex.Tok{Lex.TSpace{}, t, l, c}}, self, path, hot),
                    Bool.and(hot, False{}), Laws.unit.count(rest, Some{Lex.Tok{Lex.TSpace{}, t, l, c}}, self, hot),
                    unit.off(hot, UnitRule.cite(UnitRule.which(t, prev, UnitRule.first_tok(rest)), path)),
                    Laws.unit_walk_counts(rest, Some{Lex.Tok{Lex.TSpace{}, t, l, c}}, self, path, hot))
                case Lex.TNewline{}:
                  unit.leaf(UnitRule.op_hit(Lex.Tok{Lex.TNewline{}, t, l, c}, prev, UnitRule.first_tok(rest), path,
                    hot), UnitRule.walk(rest, Some{Lex.Tok{Lex.TNewline{}, t, l, c}}, self, path, hot),
                    Bool.and(hot, False{}), Laws.unit.count(rest, Some{Lex.Tok{Lex.TNewline{}, t, l, c}}, self, hot),
                    unit.off(hot, UnitRule.cite(UnitRule.which(t, prev, UnitRule.first_tok(rest)), path)),
                    Laws.unit_walk_counts(rest, Some{Lex.Tok{Lex.TNewline{}, t, l, c}}, self, path, hot))
                case Lex.TOp{}:
                  unit.leaf(UnitRule.op_hit(Lex.Tok{Lex.TOp{}, t, l, c}, prev, UnitRule.first_tok(rest), path, hot),
                    UnitRule.walk(rest, None{}, self, path, hot),
                    Bool.and(hot, Laws.unit.by_one(t, prev, Laws.unit.first(rest))), Laws.unit.count(rest, None{}, self,
                      hot),
                    unit.on(hot, UnitRule.cite(UnitRule.which(t, prev, UnitRule.first_tok(rest)), path),
                      Laws.unit.by_one(t, prev, Laws.unit.first(rest)), unit.opx(t, prev, rest, path)),
                    Laws.unit_walk_counts(rest, None{}, self, path, hot))
                case Lex.TColon{}:
                  unit.leaf(UnitRule.op_hit(Lex.Tok{Lex.TColon{}, t, l, c}, prev, UnitRule.first_tok(rest), path, hot),
                    UnitRule.walk(rest, Some{Lex.Tok{Lex.TColon{}, t, l, c}}, self, path, hot),
                    Bool.and(hot, False{}), Laws.unit.count(rest, Some{Lex.Tok{Lex.TColon{}, t, l, c}}, self, hot),
                    unit.off(hot, UnitRule.cite(UnitRule.which(t, prev, UnitRule.first_tok(rest)), path)),
                    Laws.unit_walk_counts(rest, Some{Lex.Tok{Lex.TColon{}, t, l, c}}, self, path, hot))
                case Lex.TEq{}:
                  unit.leaf(UnitRule.op_hit(Lex.Tok{Lex.TEq{}, t, l, c}, prev, UnitRule.first_tok(rest), path, hot),
                    UnitRule.walk(rest, Some{Lex.Tok{Lex.TEq{}, t, l, c}}, self, path, hot),
                    Bool.and(hot, False{}), Laws.unit.count(rest, Some{Lex.Tok{Lex.TEq{}, t, l, c}}, self, hot),
                    unit.off(hot, UnitRule.cite(UnitRule.which(t, prev, UnitRule.first_tok(rest)), path)),
                    Laws.unit_walk_counts(rest, Some{Lex.Tok{Lex.TEq{}, t, l, c}}, self, path, hot))
                case Lex.TBind{}:
                  unit.leaf(UnitRule.op_hit(Lex.Tok{Lex.TBind{}, t, l, c}, prev, UnitRule.first_tok(rest), path, hot),
                    UnitRule.walk(rest, Some{Lex.Tok{Lex.TBind{}, t, l, c}}, self, path, hot),
                    Bool.and(hot, False{}), Laws.unit.count(rest, Some{Lex.Tok{Lex.TBind{}, t, l, c}}, self, hot),
                    unit.off(hot, UnitRule.cite(UnitRule.which(t, prev, UnitRule.first_tok(rest)), path)),
                    Laws.unit_walk_counts(rest, Some{Lex.Tok{Lex.TBind{}, t, l, c}}, self, path, hot))
                case Lex.TArrow{}:
                  unit.leaf(UnitRule.op_hit(Lex.Tok{Lex.TArrow{}, t, l, c}, prev, UnitRule.first_tok(rest), path, hot),
                    UnitRule.walk(rest, Some{Lex.Tok{Lex.TArrow{}, t, l, c}}, self, path, hot),
                    Bool.and(hot, False{}), Laws.unit.count(rest, Some{Lex.Tok{Lex.TArrow{}, t, l, c}}, self, hot),
                    unit.off(hot, UnitRule.cite(UnitRule.which(t, prev, UnitRule.first_tok(rest)), path)),
                    Laws.unit_walk_counts(rest, Some{Lex.Tok{Lex.TArrow{}, t, l, c}}, self, path, hot))
                case Lex.TLam{}:
                  unit.leaf(UnitRule.op_hit(Lex.Tok{Lex.TLam{}, t, l, c}, prev, UnitRule.first_tok(rest), path, hot),
                    UnitRule.walk(rest, Some{Lex.Tok{Lex.TLam{}, t, l, c}}, self, path, hot),
                    Bool.and(hot, False{}), Laws.unit.count(rest, Some{Lex.Tok{Lex.TLam{}, t, l, c}}, self, hot),
                    unit.off(hot, UnitRule.cite(UnitRule.which(t, prev, UnitRule.first_tok(rest)), path)),
                    Laws.unit_walk_counts(rest, Some{Lex.Tok{Lex.TLam{}, t, l, c}}, self, path, hot))
                case Lex.TAll{}:
                  unit.leaf(UnitRule.op_hit(Lex.Tok{Lex.TAll{}, t, l, c}, prev, UnitRule.first_tok(rest), path, hot),
                    UnitRule.walk(rest, Some{Lex.Tok{Lex.TAll{}, t, l, c}}, self, path, hot),
                    Bool.and(hot, False{}), Laws.unit.count(rest, Some{Lex.Tok{Lex.TAll{}, t, l, c}}, self, hot),
                    unit.off(hot, UnitRule.cite(UnitRule.which(t, prev, UnitRule.first_tok(rest)), path)),
                    Laws.unit_walk_counts(rest, Some{Lex.Tok{Lex.TAll{}, t, l, c}}, self, path, hot))
                case Lex.TAmp{}:
                  unit.leaf(UnitRule.op_hit(Lex.Tok{Lex.TAmp{}, t, l, c}, prev, UnitRule.first_tok(rest), path, hot),
                    UnitRule.walk(rest, Some{Lex.Tok{Lex.TAmp{}, t, l, c}}, self, path, hot),
                    Bool.and(hot, False{}), Laws.unit.count(rest, Some{Lex.Tok{Lex.TAmp{}, t, l, c}}, self, hot),
                    unit.off(hot, UnitRule.cite(UnitRule.which(t, prev, UnitRule.first_tok(rest)), path)),
                    Laws.unit_walk_counts(rest, Some{Lex.Tok{Lex.TAmp{}, t, l, c}}, self, path, hot))
                case Lex.TOpen{}:
                  unit.leaf(UnitRule.op_hit(Lex.Tok{Lex.TOpen{}, t, l, c}, prev, UnitRule.first_tok(rest), path, hot),
                    UnitRule.walk(rest, Some{Lex.Tok{Lex.TOpen{}, t, l, c}}, self, path, hot),
                    Bool.and(hot, False{}), Laws.unit.count(rest, Some{Lex.Tok{Lex.TOpen{}, t, l, c}}, self, hot),
                    unit.off(hot, UnitRule.cite(UnitRule.which(t, prev, UnitRule.first_tok(rest)), path)),
                    Laws.unit_walk_counts(rest, Some{Lex.Tok{Lex.TOpen{}, t, l, c}}, self, path, hot))
                case Lex.TClose{}:
                  unit.leaf(UnitRule.op_hit(Lex.Tok{Lex.TClose{}, t, l, c}, prev, UnitRule.first_tok(rest), path, hot),
                    UnitRule.walk(rest, Some{Lex.Tok{Lex.TClose{}, t, l, c}}, self, path, hot),
                    Bool.and(hot, False{}), Laws.unit.count(rest, Some{Lex.Tok{Lex.TClose{}, t, l, c}}, self, hot),
                    unit.off(hot, UnitRule.cite(UnitRule.which(t, prev, UnitRule.first_tok(rest)), path)),
                    Laws.unit_walk_counts(rest, Some{Lex.Tok{Lex.TClose{}, t, l, c}}, self, path, hot))
                case Lex.TComma{}:
                  unit.leaf(UnitRule.op_hit(Lex.Tok{Lex.TComma{}, t, l, c}, prev, UnitRule.first_tok(rest), path, hot),
                    UnitRule.walk(rest, Some{Lex.Tok{Lex.TComma{}, t, l, c}}, self, path, hot),
                    Bool.and(hot, False{}), Laws.unit.count(rest, Some{Lex.Tok{Lex.TComma{}, t, l, c}}, self, hot),
                    unit.off(hot, UnitRule.cite(UnitRule.which(t, prev, UnitRule.first_tok(rest)), path)),
                    Laws.unit_walk_counts(rest, Some{Lex.Tok{Lex.TComma{}, t, l, c}}, self, path, hot))
        case Tree.Group{open, +kids, close}:
          match open:
            case Lex.Tok{ok, +o, ol, oc}:
              +call = String.eq(o, "(")
              +own = UnitRule.own_of(call, UnitRule.callee(prev), kids, path, hot)
              M1.fuel.three(UnitRule.walk(kids, None{}, self, path, hot), own, UnitRule.walk(rest, None{}, self, path,
                hot),
                Laws.unit.count(kids, None{}, self, hot),
                Bool.pick(Nat, Bool.and(call, Bool.and(hot, Laws.unit.call(Laws.unit.name(prev), Calls.args(kids)))),
                  1n, 0n),
                Laws.unit.count(rest, None{}, self, hot), Laws.unit_walk_counts(kids, None{}, self, path, hot),
                Equal.trans(Nat, List.length(&2, F.Finding, own),
                  Bool.pick(Nat, Bool.and(call, Bool.and(hot, Laws.unit.call(UnitRule.callee(prev), Calls.args(kids)))),
                    1n, 0n),
                  Bool.pick(Nat, Bool.and(call, Bool.and(hot, Laws.unit.call(Laws.unit.name(prev), Calls.args(kids)))),
                    1n, 0n),
                  unit.own(call, UnitRule.callee(prev), kids, path, hot),
                  Equal.cong(String, Nat, x => Bool.pick(Nat, Bool.and(call, Bool.and(hot, Laws.unit.call(x,
                    Calls.args(kids)))), 1n,
                    0n), UnitRule.callee(prev), Laws.unit.name(prev), unit.callee(prev))),
                Laws.unit_walk_counts(rest, None{}, self, path, hot))
        case Tree.Stmt{kind, +kids, +body}:
          match kind:
            case Tree.SDef{}:
              M1.fuel.three(UnitRule.walk(kids, None{}, self, path, hot), UnitRule.walk(body, None{}, self, path, hot),
                UnitRule.walk(rest, None{}, self, path, hot), Laws.unit.count(kids, None{}, self, hot),
                Laws.unit.count(body, None{}, self, hot), Laws.unit.count(rest, None{}, self, hot),
                Laws.unit_walk_counts(kids, None{}, self, path, hot), Laws.unit_walk_counts(body, None{}, self, path,
                  hot),
                Laws.unit_walk_counts(rest, None{}, self, path, hot))
            case Tree.SType{}:
              M1.fuel.three(UnitRule.walk(kids, None{}, self, path, hot), UnitRule.walk(body, None{}, self, path, hot),
                UnitRule.walk(rest, None{}, self, path, hot), Laws.unit.count(kids, None{}, self, hot),
                Laws.unit.count(body, None{}, self, hot), Laws.unit.count(rest, None{}, self, hot),
                Laws.unit_walk_counts(kids, None{}, self, path, hot), Laws.unit_walk_counts(body, None{}, self, path,
                  hot),
                Laws.unit_walk_counts(rest, None{}, self, path, hot))
            case Tree.SLaw{}:
              M1.fuel.three(UnitRule.walk(kids, None{}, self, path, hot), UnitRule.walk(body, None{}, self, path, hot),
                UnitRule.walk(rest, None{}, self, path, hot), Laws.unit.count(kids, None{}, self, hot),
                Laws.unit.count(body, None{}, self, hot), Laws.unit.count(rest, None{}, self, hot),
                Laws.unit_walk_counts(kids, None{}, self, path, hot), Laws.unit_walk_counts(body, None{}, self, path,
                  hot),
                Laws.unit_walk_counts(rest, None{}, self, path, hot))
            case Tree.SImport{}:
              M1.fuel.three(UnitRule.walk(kids, None{}, self, path, hot), UnitRule.walk(body, None{}, self, path, hot),
                UnitRule.walk(rest, None{}, self, path, hot), Laws.unit.count(kids, None{}, self, hot),
                Laws.unit.count(body, None{}, self, hot), Laws.unit.count(rest, None{}, self, hot),
                Laws.unit_walk_counts(kids, None{}, self, path, hot), Laws.unit_walk_counts(body, None{}, self, path,
                  hot),
                Laws.unit_walk_counts(rest, None{}, self, path, hot))
            case Tree.SCase{}:
              M1.fuel.three(UnitRule.walk(kids, None{}, self, path, False{}), UnitRule.walk(body, None{}, self, path,
                Bool.and(hot, Calls.calls(body, self))),
                UnitRule.walk(rest, None{}, self, path, hot), Laws.unit.count(kids, None{}, self, False{}),
                Laws.unit.count(body, None{}, self, Bool.and(hot, Calls.calls(body, self))), Laws.unit.count(rest,
                  None{}, self, hot),
                Laws.unit_walk_counts(kids, None{}, self, path, False{}), Laws.unit_walk_counts(body, None{}, self,
                  path, Bool.and(hot, Calls.calls(body, self))),
                Laws.unit_walk_counts(rest, None{}, self, path, hot))
            case Tree.SFor{}:
              M1.fuel.three(UnitRule.walk(kids, None{}, self, path, hot), UnitRule.walk(body, None{}, self, path, hot),
                UnitRule.walk(rest, None{}, self, path, hot), Laws.unit.count(kids, None{}, self, hot),
                Laws.unit.count(body, None{}, self, hot), Laws.unit.count(rest, None{}, self, hot),
                Laws.unit_walk_counts(kids, None{}, self, path, hot), Laws.unit_walk_counts(body, None{}, self, path,
                  hot),
                Laws.unit_walk_counts(rest, None{}, self, path, hot))
            case Tree.SLet{}:
              M1.fuel.three(UnitRule.walk(kids, None{}, self, path, hot), UnitRule.walk(body, None{}, self, path, hot),
                UnitRule.walk(rest, None{}, self, path, hot), Laws.unit.count(kids, None{}, self, hot),
                Laws.unit.count(body, None{}, self, hot), Laws.unit.count(rest, None{}, self, hot),
                Laws.unit_walk_counts(kids, None{}, self, path, hot), Laws.unit_walk_counts(body, None{}, self, path,
                  hot),
                Laws.unit_walk_counts(rest, None{}, self, path, hot))
            case Tree.STerm{}:
              M1.fuel.three(UnitRule.walk(kids, None{}, self, path, hot), UnitRule.walk(body, None{}, self, path, hot),
                UnitRule.walk(rest, None{}, self, path, hot), Laws.unit.count(kids, None{}, self, hot),
                Laws.unit.count(body, None{}, self, hot), Laws.unit.count(rest, None{}, self, hot),
                Laws.unit_walk_counts(kids, None{}, self, path, hot), Laws.unit_walk_counts(body, None{}, self, path,
                  hot),
                Laws.unit_walk_counts(rest, None{}, self, path, hot))
        case Tree.NNil{}:
          Laws.unit_walk_counts(rest, prev, self, path, hot)
        case Tree.NCons{x, y}:
          Laws.unit_walk_counts(rest, prev, self, path, hot)
    case Tree.Leaf{x}:
      {==}
    case Tree.Group{x, y, z}:
      {==}
    case Tree.Stmt{x, y, z}:
      {==}
    case Tree.NNil{}:
      {==}

# one def's findings: its walk when it calls itself and is not exempt
law unit.stop:
  for b: Bool
  for +body: Tree.Node
  for +name: String
  for +path: String
  {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, Bool.not(b), [],
    _u => UnitRule.walk(body, None{}, name, path, True{})))
    == Bool.pick(Nat, b, Laws.unit.count(body, None{}, name, True{}), 0n) : Nat}

def unit.stop(b, body, name, path):
  match b:
    case True{}:
      Laws.unit_walk_counts(body, None{}, name, path, True{})
    case False{}:
      {==}

# unit's def walk: the findings gathered so far, then each def's
law unit.go:
  for ds: List<&2, Calls.Def>
  for +path: String
  for +acc: List<&2, List<&2, F.Finding>>
  {List.length(&2, F.Finding, UnitRule.check.go(ds, path, acc)) == M1.pick.sum(acc, Laws.unit.defs(ds, path)) : Nat}

def unit.go(ds, path, acc):
  match ds:
    case Nil{}:
      M1.pick.rev(acc, Nil{})
    case Con{d, +rest}:
      match d:
        case Calls.Def{+name, +sig, +body}:
          +b = Bool.and(Calls.calls(body, name), Bool.not(Calls.exempt(path, sig)))
          +x = Lazy.stop(List<&2, F.Finding>, Bool.not(b), [], _u => UnitRule.walk(body, None{}, name, path, True{}))
          +cb = Bool.pick(Nat, b, Laws.unit.count(body, None{}, name, True{}), 0n)
          Equal.trans(Nat, List.length(&2, F.Finding, UnitRule.check.go(rest, path, x <> acc)),
            M1.pick.sum(acc, Nat.add(List.length(&2, F.Finding, x), Laws.unit.defs(rest, path))),
            M1.pick.sum(acc, Nat.add(cb, Laws.unit.defs(rest, path))),
            unit.go(rest, path, x <> acc),
            Equal.cong(Nat, Nat, n => M1.pick.sum(acc, Nat.add(n, Laws.unit.defs(rest, path))),
              List.length(&2, F.Finding, x), cb, unit.stop(b, body, name, path)))

def Laws.unit_counts(path, _text, _toks, tree, _bound, _items):
  unit.go(Calls.defs(tree), path, Nil{})
