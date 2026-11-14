# proofs of laws/FuelReportsLiteralBudgets.bend
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/rules/tokens.bend as T
import ../src/syntax/bind.bend as Bind
import ../src/lazy/lazy.bend as Lazy
import ../src/syntax/tree.bend as Tree
import ../src/rules/calls.bend as Calls
import ../src/rules/correctness/pick.bend as Pick
import ../src/rules/pedantic/fuel.bend as FuelRule
import ../laws/FuelReportsLiteralBudgets.bend as Laws
import ./lemmas/Pick.bend as M1

# fuel (laws/FuelReportsLiteralBudgets.bend): the rule's parameter scan is the law's, its call
# checks count the law's hits, and its walk the law's count.

# the rule's fuel parameters of one def are the law's
law fuel.of:
  for ps: List<&2, Tree.Node>
  for +name: String
  for +ii: Nat
  {FuelRule.fuels.params(ps, name, ii) == Laws.fuel.slots.of(ps, name, ii) : List<&2, FuelRule.Fuel>}

def fuel.of(ps, name, ii):
  match ps:
    case Nil{}:
      {==}
    case Con{p, rest}:
      Equal.cong(List<&2, FuelRule.Fuel>, List<&2, FuelRule.Fuel>,
        x => Bool.pick(List<&2, FuelRule.Fuel>, FuelRule.is_fuel(Calls.param_name(p)), FuelRule.Fuel{name, ii} <> x, x),
        FuelRule.fuels.params(rest, name, 1n+ii), Laws.fuel.slots.of(rest, name, 1n+ii), fuel.of(rest, name, 1n+ii))

# the rule reads the name after an arrow as the law does
law fuel.io.next:
  for nn: Tree.Node
  {FuelRule.effect.io(nn) == Laws.fuel.io.next(nn) : Bool}

def fuel.io.next(nn):
  match nn:
    case Tree.NCons{g, r}:
      match g:
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

# the rule's effect test on a header is the law's
law fuel.effect:
  for sig: Tree.Node
  {FuelRule.effect(sig) == Laws.fuel.io(sig) : Bool}

def fuel.effect(sig):
  match sig:
    case Tree.NCons{h, +rest}:
      +a = Calls.kind.leaf(~Calls.kind.arrow, h)
      Equal.trans(Bool,
        Bool.or(Bool.and(a, FuelRule.effect.io(rest)), FuelRule.effect(rest)),
        Bool.or(Bool.and(a, Laws.fuel.io.next(rest)), FuelRule.effect(rest)),
        Bool.or(Bool.and(a, Laws.fuel.io.next(rest)), Laws.fuel.io(rest)),
        Equal.cong(Bool, Bool, z => Bool.or(Bool.and(a, z), FuelRule.effect(rest)),
          FuelRule.effect.io(rest), Laws.fuel.io.next(rest), fuel.io.next(rest)),
        Equal.cong(Bool, Bool, z => Bool.or(Bool.and(a, Laws.fuel.io.next(rest)), z),
          FuelRule.effect(rest), Laws.fuel.io(rest), fuel.effect(rest)))
    case Tree.Leaf{tok}: {==}
    case Tree.Group{o, gk, cl}: {==}
    case Tree.Stmt{sk, sks, sb}: {==}
    case Tree.NNil{}: {==}

def Laws.fuel_slots(ds):
  match ds:
    case Nil{}:
      {==}
    case Con{d, +rest}:
      match d:
        case Calls.Def{+name, +sig, body}:
          +aa = FuelRule.fuels.params(FuelRule.slots(sig), name, 0n)
          +bb = Laws.fuel.slots.of(Laws.fuel.params(sig), name, 0n)
          Equal.trans(List<&2, FuelRule.Fuel>, List.append(&2, FuelRule.Fuel, aa, FuelRule.fuels(rest)),
            List.append(&2, FuelRule.Fuel, bb, FuelRule.fuels(rest)), List.append(&2, FuelRule.Fuel, bb,
              Laws.fuel.slots(rest)),
            Equal.cong(List<&2, FuelRule.Fuel>, List<&2, FuelRule.Fuel>, x => List.append(&2, FuelRule.Fuel, x,
              FuelRule.fuels(rest)),
              aa, bb, Equal.trans(List<&2, FuelRule.Fuel>, aa,
                FuelRule.fuels.params(Laws.fuel.params(sig), name, 0n), bb,
                Equal.cong(Bool, List<&2, FuelRule.Fuel>,
                  z => FuelRule.fuels.params(Bool.pick(List<&2, Tree.Node>, z, [], Calls.params(sig)), name, 0n),
                  FuelRule.effect(sig), Laws.fuel.io(sig), fuel.effect(sig)),
                fuel.of(Laws.fuel.params(sig), name, 0n))),
            Equal.cong(List<&2, FuelRule.Fuel>, List<&2, FuelRule.Fuel>, x => List.append(&2, FuelRule.Fuel, bb, x),
              FuelRule.fuels(rest), Laws.fuel.slots(rest), Laws.fuel_slots(rest)))

# a `U32.to_nat(..)` group holding one U32 literal alone is one finding when
# the call is that one, anything else none
law fuel.conv:
  for kids: Tree.Node
  for ok: Bool
  for +ll: U32
  for +cc: U32
  for +path: String
  {List.length(&2, F.Finding, FuelRule.converted(kids, ok, ll, cc, path))
    == Bool.pick(Nat, Laws.fuel.conv(kids, ok), 1n, 0n) : Nat}

def fuel.conv(kids, ok, ll, cc, path):
  match kids:
    case Tree.NCons{h, r}:
      match h:
        case Tree.Leaf{tok}:
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
                  match r:
                    case Tree.Leaf{x}:
                      {==}
                    case Tree.Group{x, y, z}:
                      {==}
                    case Tree.Stmt{x, y, z}:
                      {==}
                    case Tree.NNil{}:
                      M1.chars.one(Bool.and(ok, T.digits_ok(String.to_list(t))), F.Finding{path, ll, cc,
                        U32.from_nat(Nat.add(String.length(t), 12n)), "fuel",
                        "The fuel is fixed at U32.to_nat(" ++ t
                          ++ "), so longer input is silently cut short; derive the fuel from the input size."})
                    case Tree.NCons{x, y}:
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

# a lone Nat literal argument, or U32.to_nat of a lone U32 literal, is one
# finding, anything else none
law fuel.lit:
  for aa: Tree.Node
  for +path: String
  {List.length(&2, F.Finding, FuelRule.literal(aa, path)) == Bool.pick(Nat, Laws.fuel.lone(aa), 1n, 0n) : Nat}

def fuel.lit(aa, path):
  match aa:
    case Tree.NCons{h, r}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{k, +t, l, c}:
              match k:
                case Lex.TName{}:
                  {==}
                case Lex.TUpper{}:
                  {==}
                case Lex.TDotted{}:
                  match r:
                    case Tree.Leaf{x}:
                      {==}
                    case Tree.Group{x, y, z}:
                      {==}
                    case Tree.Stmt{x, y, z}:
                      {==}
                    case Tree.NNil{}:
                      {==}
                    case Tree.NCons{g, y}:
                      match g:
                        case Tree.Leaf{x}:
                          {==}
                        case Tree.Group{o, kids, cl}:
                          match o:
                            case Lex.Tok{ok, +ot, ol, oc}:
                              match y:
                                case Tree.Leaf{x}:
                                  {==}
                                case Tree.Group{x, w, z}:
                                  {==}
                                case Tree.Stmt{x, w, z}:
                                  {==}
                                case Tree.NNil{}:
                                  fuel.conv(kids, Bool.and(String.eq(t, "U32.to_nat"), String.eq(ot, "(")), l, c, path)
                                case Tree.NCons{x, w}:
                                  {==}
                        case Tree.Stmt{x, w, z}:
                          {==}
                        case Tree.NNil{}:
                          {==}
                        case Tree.NCons{x, w}:
                          {==}
                case Lex.TWild{}:
                  {==}
                case Lex.TKey{}:
                  {==}
                case Lex.TNum{}:
                  match r:
                    case Tree.Leaf{x}:
                      {==}
                    case Tree.Group{x, y, z}:
                      {==}
                    case Tree.Stmt{x, y, z}:
                      {==}
                    case Tree.NNil{}:
                      M1.chars.one(T.nat_ok(String.to_list(t)), F.Finding{path, l, c, U32.from_nat(String.length(t)),
                        "fuel",
                        "The fuel is fixed at " ++ t ++ ", so longer input is silently cut short; derive the fuel from the input size."})
                    case Tree.NCons{x, y}:
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

# one fuel parameter's check onto the rest's: its literal's finding when the
# def's name is the call's
law fuel.stop:
  for b: Bool
  for +l: Bool
  for +lit: List<&2, F.Finding>
  for +more: List<&2, F.Finding>
  for -m: Nat
  for e1: {List.length(&2, F.Finding, lit) == Bool.pick(Nat, l, 1n, 0n) : Nat}
  for e2: {List.length(&2, F.Finding, more) == m : Nat}
  {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, Bool.not(b), more,
    _u => List.append(&2, F.Finding, lit, more))) == Bool.pick(Nat, Bool.and(b, l), 1n+m, m) : Nat}

def fuel.stop(b, l, lit, more, m, e1, e2):
  match b:
    case True{}:
      Equal.trans(Nat, List.length(&2, F.Finding, List.append(&2, F.Finding, lit, more)),
        Nat.add(Bool.pick(Nat, l, 1n, 0n), m), Bool.pick(Nat, l, 1n+m, m),
        M1.pick.join(lit, more, Bool.pick(Nat, l, 1n, 0n), m, e1, e2), M1.fuel.addpick(l, m))
    case False{}:
      e2

# a call's findings count the law's hits
law fuel.call:
  for fs: List<&2, FuelRule.Fuel>
  for +name: String
  for +as: List<&2, Tree.Node>
  for +path: String
  {List.length(&2, F.Finding, FuelRule.call(fs, name, as, path)) == Laws.fuel.hits(fs, name, as) : Nat}

def fuel.call(fs, name, as, path):
  match fs:
    case Nil{}:
      {==}
    case Con{f, +rest}:
      match f:
        case FuelRule.Fuel{+fn, +at}:
          fuel.stop(String.eq(fn, name), Laws.fuel.lone(Calls.arg(as, at)), FuelRule.literal(Calls.arg(as, at), path),
            FuelRule.call(rest, name, as, path), Laws.fuel.hits(rest, name, as), fuel.lit(Calls.arg(as, at), path),
            fuel.call(rest, name, as, path))

# a call site: the call's findings when it counts, onto the rest's
law fuel.site:
  for hit: Bool
  for +cl: List<&2, F.Finding>
  for +more: List<&2, F.Finding>
  for -hh: Nat
  for -m: Nat
  for e1: {List.length(&2, F.Finding, cl) == hh : Nat}
  for e2: {List.length(&2, F.Finding, more) == m : Nat}
  {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, Bool.not(hit), more,
    _u => List.append(&2, F.Finding, cl, more))) == Bool.pick(Nat, hit, Nat.add(hh, m), m) : Nat}

def fuel.site(hit, cl, more, hh, m, e1, e2):
  match hit:
    case True{}:
      M1.pick.join(cl, more, hh, m, e1, e2)
    case False{}:
      e2

def Laws.fuel_walk_counts(nn, fs, self, path):
  match nn:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Leaf{tok}:
          match tok:
            case Lex.Tok{k, +t, l, c}:
              match rest:
                case Tree.NCons{h2, +r2}:
                  match h2:
                    case Tree.Group{open, +kids, close}:
                      match open:
                        case Lex.Tok{ok, +o, ol, oc}:
                          +hit = Bool.and(Bool.and(Lex.is_name(k), String.eq(o, "(")), Bool.not(String.eq(t, self)))
                          +more = List.concat(&2, F.Finding, [FuelRule.calls(kids, fs, self, path), FuelRule.calls(r2,
                            fs, self, path)])
                          +m = Nat.add(Laws.fuel.count(kids, fs, self), Laws.fuel.count(r2, fs, self))
                          fuel.site(hit, FuelRule.call(fs, t, Calls.args(kids), path), more, Laws.fuel.hits(fs, t,
                            Calls.args(kids)), m,
                            fuel.call(fs, t, Calls.args(kids), path),
                            M1.fuel.two(FuelRule.calls(kids, fs, self, path), FuelRule.calls(r2, fs, self, path),
                              Laws.fuel.count(kids, fs, self), Laws.fuel.count(r2, fs, self),
                                Laws.fuel_walk_counts(kids, fs, self, path), Laws.fuel_walk_counts(r2, fs, self, path)))
                    case Tree.Leaf{x}:
                      Laws.fuel_walk_counts(rest, fs, self, path)
                    case Tree.Stmt{x, y, z}:
                      Laws.fuel_walk_counts(rest, fs, self, path)
                    case Tree.NNil{}:
                      Laws.fuel_walk_counts(rest, fs, self, path)
                    case Tree.NCons{x, y}:
                      Laws.fuel_walk_counts(rest, fs, self, path)
                case Tree.Leaf{x}:
                  Laws.fuel_walk_counts(rest, fs, self, path)
                case Tree.Group{x, y, z}:
                  Laws.fuel_walk_counts(rest, fs, self, path)
                case Tree.Stmt{x, y, z}:
                  Laws.fuel_walk_counts(rest, fs, self, path)
                case Tree.NNil{}:
                  Laws.fuel_walk_counts(rest, fs, self, path)
        case Tree.Group{open, +kids, close}:
          M1.fuel.two(FuelRule.calls(kids, fs, self, path), FuelRule.calls(rest, fs, self, path), Laws.fuel.count(kids,
              fs,
            self), Laws.fuel.count(rest, fs, self), Laws.fuel_walk_counts(kids, fs, self, path),
              Laws.fuel_walk_counts(rest, fs, self, path))
        case Tree.Stmt{kind, +kids, +body}:
          M1.fuel.three(FuelRule.calls(kids, fs, self, path), FuelRule.calls(body, fs, self, path), FuelRule.calls(rest,
            fs, self, path), Laws.fuel.count(kids, fs, self), Laws.fuel.count(body, fs, self), Laws.fuel.count(rest, fs,
              self),
            Laws.fuel_walk_counts(kids, fs, self, path), Laws.fuel_walk_counts(body, fs, self, path),
              Laws.fuel_walk_counts(rest, fs, self, path))
        case Tree.NNil{}:
          Laws.fuel_walk_counts(rest, fs, self, path)
        case Tree.NCons{x, y}:
          Laws.fuel_walk_counts(rest, fs, self, path)
    case Tree.Leaf{x}:
      {==}
    case Tree.Group{x, y, z}:
      {==}
    case Tree.Stmt{x, y, z}:
      {==}
    case Tree.NNil{}:
      {==}

# a statement's own name, to the rule and to the law
law fuel.own:
  for mm: Maybe<&2, String>
  {FuelRule.own(mm) == Laws.fuel.own(mm) : String}

def fuel.own(mm):
  match mm:
    case None{}:
      {==}
    case Some{nm}:
      {==}

# a chain walked with the rule's self counts the law's
law fuel.self:
  for +nn: Tree.Node
  for +fs: List<&2, FuelRule.Fuel>
  for +mm: Maybe<&2, String>
  for +path: String
  {List.length(&2, F.Finding, FuelRule.calls(nn, fs, FuelRule.own(mm), path))
    == Laws.fuel.count(nn, fs, Laws.fuel.own(mm)) : Nat}

def fuel.self(nn, fs, mm, path):
  Equal.trans(Nat, List.length(&2, F.Finding, FuelRule.calls(nn, fs, FuelRule.own(mm), path)),
    Laws.fuel.count(nn, fs, FuelRule.own(mm)), Laws.fuel.count(nn, fs, Laws.fuel.own(mm)),
    Laws.fuel_walk_counts(nn, fs, FuelRule.own(mm), path),
    Equal.cong(String, Nat, x => Laws.fuel.count(nn, fs, x), FuelRule.own(mm), Laws.fuel.own(mm), fuel.own(mm)))

# the rule's statement walk counts the law's total
law fuel.go:
  for root: Tree.Node
  for +fs: List<&2, FuelRule.Fuel>
  for +path: String
  {List.length(&2, F.Finding, FuelRule.check.go(root, fs, path)) == Laws.fuel.total(root, fs) : Nat}

def fuel.go(root, fs, path):
  match root:
    case Tree.NCons{h, +rest}:
      match h:
        case Tree.Stmt{kind, +kids, +body}:
          +self = FuelRule.own(Bind.declared(kids))
          +me = Laws.fuel.own(Bind.declared(kids))
          M1.fuel.three(FuelRule.calls(kids, fs, self, path), FuelRule.calls(body, fs, self, path),
            FuelRule.check.go(rest, fs, path), Laws.fuel.count(kids, fs, me), Laws.fuel.count(body, fs, me),
            Laws.fuel.total(rest, fs), fuel.self(kids, fs, Bind.declared(kids), path),
            fuel.self(body, fs, Bind.declared(kids), path), fuel.go(rest, fs, path))
        case Tree.Leaf{x}:
          fuel.go(rest, fs, path)
        case Tree.Group{x, y, z}:
          fuel.go(rest, fs, path)
        case Tree.NNil{}:
          fuel.go(rest, fs, path)
        case Tree.NCons{x, y}:
          fuel.go(rest, fs, path)
    case Tree.Leaf{x}:
      {==}
    case Tree.Group{x, y, z}:
      {==}
    case Tree.Stmt{x, y, z}:
      {==}
    case Tree.NNil{}:
      {==}

def Laws.fuel_counts(path, _text, _toks, tree, _bound, _items):
  +ds = Calls.defs(tree)
  Equal.trans(Nat, List.length(&2, F.Finding, FuelRule.check.go(tree, FuelRule.fuels(ds), path)),
    Laws.fuel.total(tree, FuelRule.fuels(ds)), Laws.fuel.total(tree, Laws.fuel.slots(ds)),
    fuel.go(tree, FuelRule.fuels(ds), path),
    Equal.cong(List<&2, FuelRule.Fuel>, Nat, x => Laws.fuel.total(tree, x), FuelRule.fuels(ds), Laws.fuel.slots(ds),
      Laws.fuel_slots(ds)))
