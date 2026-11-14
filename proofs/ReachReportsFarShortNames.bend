# proofs of laws/ReachReportsFarShortNames.bend
import Base
import ../src/finding.bend as F
import ../src/rules/tokens.bend as T
import ../src/rules/style/reach.bend as Reach
import ../src/syntax/bind.bend as Bind
import ../src/syntax/lex.bend as Lex
import ../src/paths.bend as Paths
import ../src/lazy/lazy.bend as Lazy
import ../laws/ReachReportsFarShortNames.bend as Laws
import ./lemmas/Pick.bend as M2
import ./lemmas/HoleEarlyAnd.bend as M3

# the kinds the rule counts are the law's
law reach.kind:
  for kk: Bind.BindKind
  {Reach.kind(kk) == Laws.counted(kk) : Bool}

def reach.kind(kk):
  match kk:
    case Bind.KParam{}:
      {==}
    case Bind.KLocal{}:
      {==}
    case Bind.KPat{}:
      {==}
    case Bind.KItem{}:
      {==}
    case Bind.KCtor{}:
      {==}
    case Bind.KTypeParam{}:
      {==}
    case Bind.KField{}:
      {==}
    case Bind.KFor{}:
      {==}
    case Bind.KTypeVar{}:
      {==}

# the early-exit or of a Bool and a thunk is the plain or
law reach.or:
  for a: Bool
  for -x: Bool
  {Lazy.or_else(a, _u => x) == Bool.or(a, x) : Bool}

def reach.or(a, _x):
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# a binder kept when a test holds is found among the rest exactly when the
# test holds and it is the one looked for, or the rest holds it
law reach.keep:
  for b: Bool
  for +tl: U32
  for +tc: U32
  for +fr: List<&2, Bind.Pos>
  for +line: U32
  for +col: U32
  {Reach.reaches(Reach.far.keep(Bool.pick(Maybe<&2, Bind.Pos>, b, Some{Bind.Pos{tl, tc}}, None{}), fr), line, col)
    == Bool.or(Bool.and(b, Bool.and(U32.is_eq(tl, line), U32.is_eq(tc, col))), Reach.reaches(fr, line, col)) : Bool}

def reach.keep(b, tl, tc, fr, line, col):
  match b:
    case True{}:
      reach.or(Bool.and(U32.is_eq(tl, line), U32.is_eq(tc, col)), Reach.reaches(fr, line, col))
    case False{}:
      {==}

# one use onto uses the claim holds for
law reach.use:
  for +name: String
  for +ul: U32
  for tt: Bind.Target
  for +rest: List<&2, Bind.Use>
  for +line: U32
  for +col: U32
  for +max: U32
  for ih: {Reach.reaches(Reach.far(rest, max), line, col) == Laws.read_far(rest, line, col, max) : Bool}
  {Reach.reaches(Reach.far.keep(Reach.far.hit(name, ul, tt, max), Reach.far(rest, max)), line, col)
    == Bool.or(Laws.reads_far(name, ul, tt, line, col, max), Laws.read_far(rest, line, col, max)) : Bool}

def reach.use(name, ul, tt, rest, line, col, max, ih):
  match tt:
    case Bind.TLocal{+tl, +tc}:
      Equal.trans(Bool,
        Reach.reaches(Reach.far.keep(Bool.pick(Maybe<&2, Bind.Pos>,
          Lazy.and_then(U32.is_gt(ul, (tl + max : U32)), _u => Reach.one(name)),
          Some{Bind.Pos{tl, tc}}, None{}), Reach.far(rest, max)), line, col),
        Bool.or(Bool.and(Lazy.and_then(U32.is_gt(ul, (tl + max : U32)), _u => Reach.one(name)),
          Bool.and(U32.is_eq(tl, line), U32.is_eq(tc, col))), Reach.reaches(Reach.far(rest, max), line, col)),
        Bool.or(Bool.and(Bool.and(U32.is_gt(ul, (tl + max : U32)), Reach.one(name)),
          Bool.and(U32.is_eq(tl, line), U32.is_eq(tc, col))), Laws.read_far(rest, line, col, max)),
        reach.keep(Lazy.and_then(U32.is_gt(ul, (tl + max : U32)), _u => Reach.one(name)), tl, tc, Reach.far(rest, max),
          line, col),
        Equal.trans(Bool,
          Bool.or(Bool.and(Lazy.and_then(U32.is_gt(ul, (tl + max : U32)), _u => Reach.one(name)),
            Bool.and(U32.is_eq(tl, line), U32.is_eq(tc, col))), Reach.reaches(Reach.far(rest, max), line, col)),
          Bool.or(Bool.and(Bool.and(U32.is_gt(ul, (tl + max : U32)), Reach.one(name)),
            Bool.and(U32.is_eq(tl, line), U32.is_eq(tc, col))), Reach.reaches(Reach.far(rest, max), line, col)),
          Bool.or(Bool.and(Bool.and(U32.is_gt(ul, (tl + max : U32)), Reach.one(name)),
            Bool.and(U32.is_eq(tl, line), U32.is_eq(tc, col))), Laws.read_far(rest, line, col, max)),
          Equal.cong(Bool, Bool,
            z => Bool.or(Bool.and(z, Bool.and(U32.is_eq(tl, line), U32.is_eq(tc, col))),
              Reach.reaches(Reach.far(rest, max), line, col)),
            Lazy.and_then(U32.is_gt(ul, (tl + max : U32)), _u => Reach.one(name)),
            Bool.and(U32.is_gt(ul, (tl + max : U32)), Reach.one(name)),
            M3.hole.and(U32.is_gt(ul, (tl + max : U32)), Reach.one(name), Reach.one(name), {==})),
          Equal.cong(Bool, Bool,
            z => Bool.or(Bool.and(Bool.and(U32.is_gt(ul, (tl + max : U32)), Reach.one(name)),
              Bool.and(U32.is_eq(tl, line), U32.is_eq(tc, col))), z),
            Reach.reaches(Reach.far(rest, max), line, col), Laws.read_far(rest, line, col, max), ih)))
    case Bind.TItem{n}:
      ih
    case Bind.TQual{a, n}:
      ih
    case Bind.TFree{}:
      ih

# the binders read from afar hold the one at a line and column exactly when
# a use reads it from afar
law reach.read:
  for uses: List<&2, Bind.Use>
  for +line: U32
  for +col: U32
  for +max: U32
  {Reach.reaches(Reach.far(uses, max), line, col) == Laws.read_far(uses, line, col, max) : Bool}

def reach.read(uses, line, col, max):
  match uses:
    case Nil{}:
      {==}
    case Con{Bind.Use{name, ul, uc, tt}, +rest}:
      reach.use(name, ul, tt, rest, line, col, max, reach.read(rest, line, col, max))

# the rule's early-exit test is the law's plain one
law reach.flagged:
  for +uses: List<&2, Bind.Use>
  for +line: U32
  for +col: U32
  for +kk: Bind.BindKind
  for +nm: String
  for +note: String
  for +ps: List<&2, U32>
  for +item: U32
  for +max: U32
  {Reach.flagged(Reach.far(uses, max), line, col, kk, nm, note, ps, item)
    == Laws.carried(kk, nm, line, col, note, uses, ps, item, max) : Bool}

def reach.flagged(uses, line, col, kk, nm, note, ps, item, max):
  Equal.trans(Bool,
    Reach.flagged(Reach.far(uses, max), line, col, kk, nm, note, ps, item),
    Bool.and(Reach.reaches(Reach.far(uses, max), line, col),
      Bool.and(Laws.counted(kk), Bool.and(Bool.not(Reach.allowed(kk, nm, note)), Bool.not(Reach.has(ps, item))))),
    Laws.carried(kk, nm, line, col, note, uses, ps, item, max),
    M3.hole.and(Reach.reaches(Reach.far(uses, max), line, col),
      Lazy.and_then(Reach.kind(kk),
        _v => Lazy.and_then(Bool.not(Reach.allowed(kk, nm, note)), _w => Bool.not(Reach.has(ps, item)))),
      Bool.and(Laws.counted(kk), Bool.and(Bool.not(Reach.allowed(kk, nm, note)), Bool.not(Reach.has(ps, item)))),
      Equal.trans(Bool,
        Lazy.and_then(Reach.kind(kk),
          _v => Lazy.and_then(Bool.not(Reach.allowed(kk, nm, note)), _w => Bool.not(Reach.has(ps, item)))),
        Bool.and(Reach.kind(kk), Bool.and(Bool.not(Reach.allowed(kk, nm, note)), Bool.not(Reach.has(ps, item)))),
        Bool.and(Laws.counted(kk), Bool.and(Bool.not(Reach.allowed(kk, nm, note)), Bool.not(Reach.has(ps, item)))),
        M3.hole.and(Reach.kind(kk),
          Lazy.and_then(Bool.not(Reach.allowed(kk, nm, note)), _w => Bool.not(Reach.has(ps, item))),
          Bool.and(Bool.not(Reach.allowed(kk, nm, note)), Bool.not(Reach.has(ps, item))),
          M3.hole.and(Bool.not(Reach.allowed(kk, nm, note)), Bool.not(Reach.has(ps, item)),
            Bool.not(Reach.has(ps, item)), {==})),
        Equal.cong(Bool, Bool,
          z => Bool.and(z, Bool.and(Bool.not(Reach.allowed(kk, nm, note)), Bool.not(Reach.has(ps, item)))),
          Reach.kind(kk), Laws.counted(kk), reach.kind(kk)))),
    Equal.cong(Bool, Bool,
      z => Bool.and(z,
        Bool.and(Laws.counted(kk), Bool.and(Bool.not(Reach.allowed(kk, nm, note)), Bool.not(Reach.has(ps, item))))),
      Reach.reaches(Reach.far(uses, max), line, col), Laws.read_far(uses, line, col, max), reach.read(uses, line,
        col, max)))

# a finding in front when the test holds adds one to the count
law reach.found:
  for b: Bool
  for -nm: String
  for -line: U32
  for -col: U32
  for -path: String
  for -max: U32
  for -more: List<&2, F.Finding>
  for -m: Nat
  for ih: {List.length(&2, F.Finding, more) == m : Nat}
  {List.length(&2, F.Finding, Reach.found(b, nm, line, col, path, max, more)) == Bool.pick(Nat, b, 1n+m, m) : Nat}

def reach.found(b, _nm, _line, _col, _path, _max, more, m, ih):
  match b:
    case True{}:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, F.Finding, more), m, ih)
    case False{}:
      ih

# one binder onto binders the count holds for
law reach.step:
  for +nm: String
  for +line: U32
  for +col: U32
  for +kk: Bind.BindKind
  for +note: String
  for +rest: List<&2, Bind.Bind>
  for +uses: List<&2, Bind.Use>
  for +ps: List<&2, U32>
  for +path: String
  for +item: U32
  for +max: U32
  for ih: {List.length(&2, F.Finding,
      Reach.check.go(rest, Reach.far(uses, max), ps, path, Reach.at_item(kk, line, item), max))
    == Laws.far_count(rest, uses, ps, Reach.at_item(kk, line, item), max) : Nat}
  {List.length(&2, F.Finding,
      Reach.check.go(Bind.Bind{nm, line, col, kk, note} <> rest, Reach.far(uses, max), ps, path, item, max))
    == Laws.far_count(Bind.Bind{nm, line, col, kk, note} <> rest, uses, ps, item, max) : Nat}

def reach.step(nm, line, col, kk, note, rest, uses, ps, path, item, max, ih):
  Equal.trans(Nat,
    List.length(&2, F.Finding,
      Reach.check.go(Bind.Bind{nm, line, col, kk, note} <> rest, Reach.far(uses, max), ps, path, item, max)),
    Bool.pick(Nat, Reach.flagged(Reach.far(uses, max), line, col, kk, nm, note, ps, Reach.at_item(kk, line, item)),
      1n+Laws.far_count(rest, uses, ps, Reach.at_item(kk, line, item), max),
      Laws.far_count(rest, uses, ps, Reach.at_item(kk, line, item), max)),
    Laws.far_count(Bind.Bind{nm, line, col, kk, note} <> rest, uses, ps, item, max),
    reach.found(Reach.flagged(Reach.far(uses, max), line, col, kk, nm, note, ps, Reach.at_item(kk, line, item)),
      nm, line, col, path, max, Reach.check.go(rest, Reach.far(uses, max), ps, path, Reach.at_item(kk, line, item),
        max),
      Laws.far_count(rest, uses, ps, Reach.at_item(kk, line, item), max), ih),
    Equal.cong(Bool, Nat,
      z => Bool.pick(Nat, z, 1n+Laws.far_count(rest, uses, ps, Reach.at_item(kk, line, item), max),
        Laws.far_count(rest, uses, ps, Reach.at_item(kk, line, item), max)),
      Reach.flagged(Reach.far(uses, max), line, col, kk, nm, note, ps, Reach.at_item(kk, line, item)),
      Laws.carried(kk, nm, line, col, note, uses, ps, Reach.at_item(kk, line, item), max),
      reach.flagged(uses, line, col, kk, nm, note, ps, Reach.at_item(kk, line, item), max)))

# the walk counts the binders the law counts
law reach.go:
  for binds: List<&2, Bind.Bind>
  for +uses: List<&2, Bind.Use>
  for +ps: List<&2, U32>
  for +path: String
  for +item: U32
  for +max: U32
  {List.length(&2, F.Finding, Reach.check.go(binds, Reach.far(uses, max), ps, path, item, max))
    == Laws.far_count(binds, uses, ps, item, max) : Nat}

def reach.go(binds, uses, ps, path, item, max):
  match binds:
    case Nil{}:
      {==}
    case Con{Bind.Bind{+nm, +line, +col, +kk, +note}, +rest}:
      reach.step(nm, line, col, kk, note, rest, uses, ps, path, item, max,
        reach.go(rest, uses, ps, path, Reach.at_item(kk, line, item), max))

# with no binder read from afar the walk finds nothing
law reach.none:
  for binds: List<&2, Bind.Bind>
  for +ps: List<&2, U32>
  for +path: String
  for +item: U32
  for +max: U32
  {Reach.check.go(binds, Nil{}, ps, path, item, max) == Nil{} : List<&2, F.Finding>}

def reach.none(binds, ps, path, item, max):
  match binds:
    case Nil{}:
      {==}
    case Con{Bind.Bind{nm, +line, col, +kk, note}, rest}:
      reach.none(rest, ps, path, Reach.at_item(kk, line, item), max)

# the shortcut on no far binder is the walk
law reach.far:
  for fr: List<&2, Bind.Pos>
  for +binds: List<&2, Bind.Bind>
  for +toks: List<&2, Lex.Tok>
  for +path: String
  for +max: U32
  {Reach.check.far(fr, binds, toks, path, max)
    == Reach.check.go(binds, fr, Reach.proofs(T.sig(toks)), path, 0, max) : List<&2, F.Finding>}

def reach.far(fr, binds, toks, path, max):
  match fr:
    case Nil{}:
      Equal.sym(List<&2, F.Finding>, Reach.check.go(binds, Nil{}, Reach.proofs(T.sig(toks)), path, 0, max), Nil{},
        reach.none(binds, Reach.proofs(T.sig(toks)), path, 0, max))
    case Con{pp, rest}:
      {==}

def Laws.reach_counts(binds, uses, toks, path, max):
  M2.param.stop(Paths.is_proof(path), Reach.check.far(Reach.far(uses, max), binds, toks, path, max),
    Laws.far_count(binds, uses, Reach.proofs(T.sig(toks)), 0, max),
    Equal.trans(Nat,
      List.length(&2, F.Finding, Reach.check.far(Reach.far(uses, max), binds, toks, path, max)),
      List.length(&2, F.Finding, Reach.check.go(binds, Reach.far(uses, max), Reach.proofs(T.sig(toks)), path, 0, max)),
      Laws.far_count(binds, uses, Reach.proofs(T.sig(toks)), 0, max),
      Equal.cong(List<&2, F.Finding>, Nat, z => List.length(&2, F.Finding, z),
        Reach.check.far(Reach.far(uses, max), binds, toks, path, max),
        Reach.check.go(binds, Reach.far(uses, max), Reach.proofs(T.sig(toks)), path, 0, max),
        reach.far(Reach.far(uses, max), binds, toks, path, max)),
      reach.go(binds, uses, Reach.proofs(T.sig(toks)), path, 0, max)))

# a test that fails keeps no binder
law reach.miss:
  for b: Bool
  for -o: Bool
  for -tl: U32
  for -tc: U32
  for e: {Bool.and(b, o) == False{} : Bool}
  {Bool.pick(Maybe<&2, Bind.Pos>, Lazy.and_then(b, _u => o), Some{Bind.Pos{tl, tc}}, None{}) == None{}
    : Maybe<&2, Bind.Pos>}

def reach.miss(b, o, tl, tc, e):
  s = Equal.sym(Bool, Lazy.and_then(b, _u => o), False{},
    Equal.trans(Bool, Lazy.and_then(b, _u => o), Bool.and(b, o), False{}, M3.hole.and(b, o, o, {==}), e))
  %s : {Bool.pick(Maybe<&2, Bind.Pos>, _, Some{Bind.Pos{tl, tc}}, None{}) == None{} : Maybe<&2, Bind.Pos>}
  {==}

def Laws.reach_near_use_is_not_far(name, line, tl, tc, max, e):
  reach.miss(U32.is_gt(line, (tl + max : U32)), Reach.one(name), tl, tc,
    Equal.cong(Bool, Bool, z => Bool.and(z, Reach.one(name)), U32.is_gt(line, (tl + max : U32)), False{}, e))

# anything and False is False
law reach.and_false:
  for b: Bool
  {Bool.and(b, False{}) == False{} : Bool}

def reach.and_false(b):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.reach_longer_name_is_not_far(name, line, tl, tc, max, e):
  reach.miss(U32.is_gt(line, (tl + max : U32)), Reach.one(name), tl, tc,
    Equal.trans(Bool, Bool.and(U32.is_gt(line, (tl + max : U32)), Reach.one(name)),
      Bool.and(U32.is_gt(line, (tl + max : U32)), False{}), False{},
      Equal.cong(Bool, Bool, z => Bool.and(U32.is_gt(line, (tl + max : U32)), z), Reach.one(name), False{}, e),
      reach.and_false(U32.is_gt(line, (tl + max : U32)))))

# an early exit whose other way is Nil is Nil either way
law reach.stop:
  for b: Bool
  {Lazy.stop(List<&2, F.Finding>, b, Nil{}, _u => Nil{}) == Nil{} : List<&2, F.Finding>}

def reach.stop(b):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.reach_silent_without_far_uses(binds, uses, toks, path, max, e):
  Equal.trans(List<&2, F.Finding>,
    Reach.check.on(binds, uses, toks, path, max),
    Lazy.stop(List<&2, F.Finding>, Paths.is_proof(path), Nil{}, _u => Nil{}),
    Nil{},
    Equal.cong(List<&2, Bind.Pos>, List<&2, F.Finding>,
      z => Lazy.stop(List<&2, F.Finding>, Paths.is_proof(path), Nil{}, _u => Reach.check.far(z, binds, toks, path,
        max)),
      Reach.far(uses, max), Nil{}, e),
    reach.stop(Paths.is_proof(path)))

# every char of the `n`s is `n`
law reach.ens.all:
  for kn: Nat
  {Reach.one.all(Laws.ens(kn), 'n') == True{} : Bool}

def reach.ens.all(kn):
  match kn:
    case 0n:
      {==}
    case 1n+p:
      reach.ens.all(p)

# the `n`s are one character
law reach.ens.one:
  for kn: Nat
  {Reach.one.go(Laws.ens(kn)) == True{} : Bool}

def reach.ens.one(kn):
  match kn:
    case 0n:
      {==}
    case 1n+p:
      reach.ens.all(p)

def Laws.reach_repeated_letter_is_one(kn, un):
  match un:
    case 0n:
      reach.ens.one(kn)
    case 1n+p:
      Laws.reach_repeated_letter_is_one(kn, p)

# `_` after `n` are `n` or `_`
law reach.tail.under:
  for un: Nat
  {Reach.one.all(Laws.unders(un, Nil{}), 'n') == True{} : Bool}

def reach.tail.under(un):
  match un:
    case 0n:
      {==}
    case 1n+p:
      reach.tail.under(p)

# the `n`s and then `_` are each `n` or `_`
law reach.tail.all:
  for kn: Nat
  for un: Nat
  {Reach.one.all(List.append(&2, Char, Laws.ens(kn), Laws.unders(un, Nil{})), 'n') == True{} : Bool}

def reach.tail.all(kn, un):
  match kn:
    case 0n:
      reach.tail.under(un)
    case 1n+p:
      reach.tail.all(p, un)

def Laws.reach_trailing_underscores_keep_one(kn, un):
  match kn:
    case 0n:
      reach.tail.under(un)
    case 1n+p:
      reach.tail.all(p, un)

# an `x` after the `n`s is not `n`
law reach.two.all:
  for kn: Nat
  for rest: List<&2, Char>
  {Reach.one.all(List.append(&2, Char, Laws.ens(kn), 'x' <> rest), 'n') == False{} : Bool}

def reach.two.all(kn, rest):
  match kn:
    case 0n:
      {==}
    case 1n+p:
      reach.two.all(p, rest)

# the `n`s and then an `x` are two characters
law reach.two.one:
  for kn: Nat
  for rest: List<&2, Char>
  {Reach.one.go(List.append(&2, Char, Laws.ens(kn), 'x' <> rest)) == False{} : Bool}

def reach.two.one(kn, rest):
  match kn:
    case 0n:
      {==}
    case 1n+p:
      reach.two.all(p, rest)

def Laws.reach_second_letter_makes_two(kn, un, rest):
  match un:
    case 0n:
      reach.two.one(kn, rest)
    case 1n+p:
      Laws.reach_second_letter_makes_two(kn, p, rest)

def Laws.reach_underscores_are_none(un):
  match un:
    case 0n:
      {==}
    case 1n+p:
      Laws.reach_underscores_are_none(p)
