# proofs of laws/IdleReportsParametersOnlyPassedBack.bend
import Base
import ../src/finding.bend as F
import ../src/paths.bend as Paths
import ../src/src.bend as Src
import ../src/lazy/lazy.bend as Lazy
import ../src/syntax/lex.bend as Lex
import ../src/syntax/tree.bend as Tree
import ../src/rules/calls.bend as Calls
import ../src/rules/suspicious/idle.bend as Idle
import ../laws/IdleReportsParametersOnlyPassedBack.bend as Laws
import ./lemmas/LawFileExemptions.bend as M1
import ./lemmas/PublishComparisons.bend as M2

# idle (laws/IdleReportsParametersOnlyPassedBack.bend). The count goes parameter by parameter and def
# by def: a parameter adds one finding exactly when it is idle, a def its
# parameters' when it is judged. The rest are the tests the rule is made
# of, each read off one hypothesis.

# nothing and False is False
law idle.and_f:
  for x: Bool
  {Bool.and(x, False{}) == False{} : Bool}

def idle.and_f(x):
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

# under two tests
law idle.and2_f:
  for x: Bool
  for y: Bool
  {Bool.and(x, Bool.and(y, False{})) == False{} : Bool}

def idle.and2_f(x, y):
  match x:
    case True{}:
      idle.and_f(y)
    case False{}:
      {==}

# under three
law idle.and3_f:
  for x: Bool
  for y: Bool
  for z: Bool
  {Bool.and(x, Bool.and(y, Bool.and(z, False{}))) == False{} : Bool}

def idle.and3_f(x, y, z):
  match x:
    case True{}:
      idle.and2_f(y, z)
    case False{}:
      {==}

# a finding is added exactly when the parameter is idle
law idle.found:
  for hit: Bool
  for -nm: String
  for -l: U32
  for -c: U32
  for -name: String
  for -path: String
  for -more: List<&2, F.Finding>
  for -m: Nat
  for ih: {List.length(&2, F.Finding, more) == m : Nat}
  {List.length(&2, F.Finding, Idle.found(hit, nm, l, c, name, path, more)) == Bool.pick(Nat, hit, 1n+m, m) : Nat}

def idle.found(hit, _nm, _l, _c, _name, _path, more, m, ih):
  match hit:
    case True{}:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, F.Finding, more), m, ih)
    case False{}:
      ih

# a parameter adds one finding exactly when the law counts it
law idle.param:
  for m: Maybe<&2, Lex.Tok>
  for p: Tree.Node
  for slot: Nat
  for sig: Tree.Node
  for body: Tree.Node
  for +name: String
  for -path: String
  for -more: List<&2, F.Finding>
  for -k: Nat
  for ih: {List.length(&2, F.Finding, more) == k : Nat}
  {List.length(&2, F.Finding, Idle.param(m, p, slot, sig, body, name, path, more))
    == Bool.pick(Nat, Laws.hit(m, p, slot, sig, body, name), 1n+k, k) : Nat}

def idle.param(m, p, slot, sig, body, name, path, more, k, ih):
  match m:
    case None{}:
      ih
    case Some{Lex.Tok{_kk, +nm, l, c}}:
      idle.found(Idle.idle(p, slot, sig, body, nm, name), nm, l, c, name, path, more, k, ih)

# the parameters add what the law counts of them
law idle.params:
  for ps: List<&2, Tree.Node>
  for +slot: Nat
  for +sig: Tree.Node
  for +body: Tree.Node
  for +name: String
  for +path: String
  for -more: List<&2, F.Finding>
  for -after: Nat
  for ih: {List.length(&2, F.Finding, more) == after : Nat}
  {List.length(&2, F.Finding, Idle.params(ps, slot, sig, body, name, path, more))
    == Laws.idle_params(ps, slot, sig, body, name, after) : Nat}

def idle.params(ps, slot, sig, body, name, path, more, after, ih):
  match ps:
    case Nil{}:
      ih
    case Con{+p, +rest}:
      idle.param(Idle.named(p), p, slot, sig, body, name, path,
        Idle.params(rest, 1n+slot, sig, body, name, path, more),
        Laws.idle_params(rest, 1n+slot, sig, body, name, after),
        idle.params(rest, 1n+slot, sig, body, name, path, more, after, ih))

# a def adds its parameters' findings when it is judged, and none when not
law idle.step:
  for x: Bool
  for -hits: List<&2, F.Finding>
  for -n: Nat
  for -more: List<&2, F.Finding>
  for -m: Nat
  for e: {List.length(&2, F.Finding, hits) == n : Nat}
  for ih: {List.length(&2, F.Finding, more) == m : Nat}
  {List.length(&2, F.Finding, Lazy.stop(List<&2, F.Finding>, Bool.not(x), more, _u => hits))
    == Bool.pick(Nat, x, n, m) : Nat}

def idle.step(x, _hits, _n, _more, _m, e, ih):
  match x:
    case True{}:
      e
    case False{}:
      ih

def Laws.idle_counts(ds, path):
  match ds:
    case Nil{}:
      {==}
    case Con{Calls.Def{+name, +sig, +body}, +rest}:
      idle.step(Idle.judged(path, sig, body, name),
        Idle.params(Calls.params(sig), 0n, sig, body, name, path, Idle.check.go(rest, path)),
        Laws.idle_params(Calls.params(sig), 0n, sig, body, name, Laws.idle_count(rest, path)),
        Idle.check.go(rest, path), Laws.idle_count(rest, path),
        idle.params(Calls.params(sig), 0n, sig, body, name, path, Idle.check.go(rest, path),
          Laws.idle_count(rest, path), Laws.idle_counts(rest, path)), Laws.idle_counts(rest, path))

def Laws.idle_cites_parameter(_nm, _l, _c, _name, _path):
  {==}

# the walk gathers nothing in a law file
law idle.none:
  for ds: List<&2, Calls.Def>
  for +path: String
  for +e: {Paths.is_law_file(path) == True{} : Bool}
  {Idle.check.go(ds, path) == Nil{} : List<&2, F.Finding>}

def idle.none(ds, path, e):
  match ds:
    case Nil{}:
      {==}
    case Con{Calls.Def{+name, +sig, +body}, +rest}:
      s = Equal.sym(Bool, Calls.exempt(path, sig), True{}, M1.ex.calls(path, sig, e))
      %s : {Lazy.stop(List<&2, F.Finding>, Bool.not(Bool.and(Bool.not(_), Calls.calls(body, name))),
          Idle.check.go(rest, path),
          _u => Idle.params(Calls.params(sig), 0n, sig, body, name, path, Idle.check.go(rest, path)))
        == Nil{} : List<&2, F.Finding>}
      idle.none(rest, path, e)

def Laws.idle_exempt(path, _text, _toks, tree, _bound, _items, e):
  idle.none(Calls.defs(tree), path, e)

def Laws.role_idle(path, text, toks, tree, bound, items):
  M1.role.skip_named(path, _u => Idle.check(Src.Src{path, text, toks, tree, bound, items}),
    e => Laws.idle_exempt(path, text, toks, tree, bound, items, e))

def Laws.judged_skips_exempt(path, sig, body, name, e):
  s = Equal.sym(Bool, Calls.exempt(path, sig), True{}, e)
  %s : {Bool.and(Bool.not(_), Calls.calls(body, name)) == False{} : Bool}
  {==}

def Laws.judged_skips_plain_def(path, sig, body, name, e):
  s = Equal.sym(Bool, Calls.calls(body, name), False{}, e)
  %s : {Bool.and(Bool.not(Calls.exempt(path, sig)), _) == False{} : Bool}
  idle.and_f(Bool.not(Calls.exempt(path, sig)))

def Laws.idle_holds(p, slot, sig, body, nm, name, e1, e2, e3, e4):
  s1 = Equal.sym(Bool, Idle.counts(p, nm), True{}, e1)
  %s1 : {Bool.and(_, Bool.and(Nat.is_eq(Idle.spelled(sig, nm), 1n),
      Bool.and(Bool.not(Nat.is_eq(Idle.spelled(body, nm), 0n)),
        Bool.not(Idle.stray(body, Idle.AOut{}, slot, nm, name))))) == True{} : Bool}
  s2 = Equal.sym(Bool, Nat.is_eq(Idle.spelled(sig, nm), 1n), True{}, e2)
  %s2 : {Bool.and(_, Bool.and(Bool.not(Nat.is_eq(Idle.spelled(body, nm), 0n)),
      Bool.not(Idle.stray(body, Idle.AOut{}, slot, nm, name)))) == True{} : Bool}
  s3 = Equal.sym(Bool, Nat.is_eq(Idle.spelled(body, nm), 0n), False{}, e3)
  %s3 : {Bool.and(Bool.not(_), Bool.not(Idle.stray(body, Idle.AOut{}, slot, nm, name))) == True{} : Bool}
  s4 = Equal.sym(Bool, Idle.stray(body, Idle.AOut{}, slot, nm, name), False{}, e4)
  %s4 : {Bool.not(_) == True{} : Bool}
  {==}

def Laws.idle_skips_uncounted(p, slot, sig, body, nm, name, e):
  s = Equal.sym(Bool, Idle.counts(p, nm), False{}, e)
  %s : {Bool.and(_, Bool.and(Nat.is_eq(Idle.spelled(sig, nm), 1n),
      Bool.and(Bool.not(Nat.is_eq(Idle.spelled(body, nm), 0n)),
        Bool.not(Idle.stray(body, Idle.AOut{}, slot, nm, name))))) == False{} : Bool}
  {==}

def Laws.idle_skips_named_again(p, slot, sig, body, nm, name, e):
  s = Equal.sym(Bool, Nat.is_eq(Idle.spelled(sig, nm), 1n), False{}, e)
  %s : {Bool.and(Idle.counts(p, nm), Bool.and(_,
      Bool.and(Bool.not(Nat.is_eq(Idle.spelled(body, nm), 0n)),
        Bool.not(Idle.stray(body, Idle.AOut{}, slot, nm, name))))) == False{} : Bool}
  idle.and_f(Idle.counts(p, nm))

def Laws.idle_skips_unread(p, slot, sig, body, nm, name, e):
  s = Equal.sym(Bool, Nat.is_eq(Idle.spelled(body, nm), 0n), True{}, e)
  %s : {Bool.and(Idle.counts(p, nm), Bool.and(Nat.is_eq(Idle.spelled(sig, nm), 1n),
      Bool.and(Bool.not(_), Bool.not(Idle.stray(body, Idle.AOut{}, slot, nm, name))))) == False{} : Bool}
  idle.and2_f(Idle.counts(p, nm), Nat.is_eq(Idle.spelled(sig, nm), 1n))

def Laws.idle_skips_stray(p, slot, sig, body, nm, name, e):
  s = Equal.sym(Bool, Idle.stray(body, Idle.AOut{}, slot, nm, name), True{}, e)
  %s : {Bool.and(Idle.counts(p, nm), Bool.and(Nat.is_eq(Idle.spelled(sig, nm), 1n),
      Bool.and(Bool.not(Nat.is_eq(Idle.spelled(body, nm), 0n)), Bool.not(_)))) == False{} : Bool}
  idle.and3_f(Idle.counts(p, nm), Nat.is_eq(Idle.spelled(sig, nm), 1n),
    Bool.not(Nat.is_eq(Idle.spelled(body, nm), 0n)))

def Laws.counts_skips_ignored(p, nm, e):
  s = Equal.sym(Bool, String.starts_with(nm, "_"), True{}, e)
  %s : {Bool.and(Calls.is_live(p), Bool.not(_)) == False{} : Bool}
  idle.and_f(Calls.is_live(p))

def Laws.counts_skips_unlive(p, nm, e):
  s = Equal.sym(Bool, Calls.is_live(p), False{}, e)
  %s : {Bool.and(_, Bool.not(String.starts_with(nm, "_"))) == False{} : Bool}
  {==}

# anything or True is True
law idle.or_t:
  for x: Bool
  {Bool.or(x, True{}) == True{} : Bool}

def idle.or_t(x):
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.reads_sees_the_name(k, nm, e):
  s = Equal.sym(Bool, Lex.is_name(k), True{}, e)
  %s : {Bool.and(_, Bool.or(String.eq(nm, nm), String.starts_with(nm, nm ++ "."))) == True{} : Bool}
  r = Equal.sym(Bool, String.eq(nm, nm), True{}, M2.pub.seq_refl(nm))
  %r : {Bool.or(_, String.starts_with(nm, nm ++ ".")) == True{} : Bool}
  {==}

def Laws.reads_sees_dotted_name(k, t, nm, e, d):
  s = Equal.sym(Bool, Lex.is_name(k), True{}, e)
  %s : {Bool.and(_, Bool.or(String.eq(t, nm), String.starts_with(t, nm ++ "."))) == True{} : Bool}
  r = Equal.sym(Bool, String.starts_with(t, nm ++ "."), True{}, d)
  %r : {Bool.or(String.eq(t, nm), _) == True{} : Bool}
  idle.or_t(String.eq(t, nm))

def Laws.reads_skips_other_name(k, t, nm, e, d):
  s = Equal.sym(Bool, String.eq(t, nm), False{}, e)
  %s : {Bool.and(Lex.is_name(k), Bool.or(_, String.starts_with(t, nm ++ "."))) == False{} : Bool}
  r = Equal.sym(Bool, String.starts_with(t, nm ++ "."), False{}, d)
  %r : {Bool.and(Lex.is_name(k), _) == False{} : Bool}
  idle.and_f(Lex.is_name(k))

def Laws.reads_skips_other_token(k, t, nm, e):
  s = Equal.sym(Bool, Lex.is_name(k), False{}, e)
  %s : {Bool.and(_, Bool.or(String.eq(t, nm), String.starts_with(t, nm ++ "."))) == False{} : Bool}
  {==}

def Laws.spelled_counts_reading(k, t, _l, _c, nm, e):
  s = Equal.sym(Bool, Idle.reads(k, t, nm), True{}, e)
  %s : {Bool.pick(Nat, _, 1n, 0n) == 1n : Nat}
  {==}

def Laws.spelled_skips_other_leaf(k, t, _l, _c, nm, e):
  s = Equal.sym(Bool, Idle.reads(k, t, nm), False{}, e)
  %s : {Bool.pick(Nat, _, 1n, 0n) == 0n : Nat}
  {==}

def Laws.spelled_adds_chain(_h, _rest, _nm):
  {==}

def Laws.spelled_reads_group(_open, _kids, _cl, _nm):
  {==}

def Laws.spelled_adds_statement(_sk, _kids, _body, _nm):
  {==}

def Laws.named_takes_lowercase_name(_t, _l, _c, _rest):
  {==}

def Laws.named_stops_at_colon(_t, _l, _c, _rest):
  {==}

def Laws.named_passes_sign(_t, _l, _c, _rest):
  {==}

def Laws.stray_sees_reading_outside(k, t, _l, _c, at, slot, nm, _name, e, o):
  s = Equal.sym(Bool, Idle.reads(k, t, nm), True{}, e)
  %s : {Bool.and(_, Bool.not(Idle.own(at, slot))) == True{} : Bool}
  r = Equal.sym(Bool, Idle.own(at, slot), False{}, o)
  %r : {Bool.not(_) == True{} : Bool}
  {==}

def Laws.stray_passes_own_argument(k, t, _l, _c, at, slot, nm, _name, o):
  r = Equal.sym(Bool, Idle.own(at, slot), True{}, o)
  %r : {Bool.and(Idle.reads(k, t, nm), Bool.not(_)) == False{} : Bool}
  idle.and_f(Idle.reads(k, t, nm))

def Laws.stray_passes_other_leaf(k, t, _l, _c, at, slot, nm, _name, e):
  s = Equal.sym(Bool, Idle.reads(k, t, nm), False{}, e)
  %s : {Bool.and(_, Bool.not(Idle.own(at, slot))) == False{} : Bool}
  {==}

def Laws.stray_enters_self_call(k, _l, _c, _ko, _lo, _co, kids, _cl, rest, at, slot, nm, name):
  s = Equal.sym(Bool, String.eq(name, name), True{}, M2.pub.seq_refl(name))
  %s : {Bool.or(Bool.and(Idle.reads(k, name, nm), Bool.not(Idle.own(at, slot))),
      Bool.or(
        Idle.stray(kids,
          Bool.pick(Idle.At, _, Idle.AArg{0n}, Idle.inner(Idle.past(Lex.is_comma(k), at), slot)), slot, nm, name),
        Idle.stray(rest, Idle.past(Lex.is_comma(k), at), slot, nm, name)))
    == Bool.or(Bool.and(Idle.reads(k, name, nm), Bool.not(Idle.own(at, slot))),
      Bool.or(Idle.stray(kids, Idle.AArg{0n}, slot, nm, name),
        Idle.stray(rest, Idle.past(Lex.is_comma(k), at), slot, nm, name))) : Bool}
  {==}

def Laws.stray_stays_in_other_call(k, t, _l, _c, _ko, o, _lo, _co, kids, _cl, rest, at, slot, nm, name, e):
  s = Equal.sym(Bool, String.eq(t, name), False{}, e)
  %s : {Bool.or(Bool.and(Idle.reads(k, t, nm), Bool.not(Idle.own(at, slot))),
      Bool.or(
        Idle.stray(kids,
          Bool.pick(Idle.At, Bool.and(String.eq(o, "("), _), Idle.AArg{0n},
            Idle.inner(Idle.past(Lex.is_comma(k), at), slot)), slot, nm, name),
        Idle.stray(rest, Idle.past(Lex.is_comma(k), at), slot, nm, name)))
    == Bool.or(Bool.and(Idle.reads(k, t, nm), Bool.not(Idle.own(at, slot))),
      Bool.or(Idle.stray(kids, Idle.inner(Idle.past(Lex.is_comma(k), at), slot), slot, nm, name),
        Idle.stray(rest, Idle.past(Lex.is_comma(k), at), slot, nm, name))) : Bool}
  a = Equal.sym(Bool, Bool.and(String.eq(o, "("), False{}), False{}, idle.and_f(String.eq(o, "(")))
  %a : {Bool.or(Bool.and(Idle.reads(k, t, nm), Bool.not(Idle.own(at, slot))),
      Bool.or(
        Idle.stray(kids,
          Bool.pick(Idle.At, _, Idle.AArg{0n}, Idle.inner(Idle.past(Lex.is_comma(k), at), slot)), slot, nm, name),
        Idle.stray(rest, Idle.past(Lex.is_comma(k), at), slot, nm, name)))
    == Bool.or(Bool.and(Idle.reads(k, t, nm), Bool.not(Idle.own(at, slot))),
      Bool.or(Idle.stray(kids, Idle.inner(Idle.past(Lex.is_comma(k), at), slot), slot, nm, name),
        Idle.stray(rest, Idle.past(Lex.is_comma(k), at), slot, nm, name))) : Bool}
  {==}

def Laws.stray_stays_in_other_bracket(k, t, _l, _c, _ko, o, _lo, _co, kids, _cl, rest, at, slot, nm, name, e):
  s = Equal.sym(Bool, String.eq(o, "("), False{}, e)
  %s : {Bool.or(Bool.and(Idle.reads(k, t, nm), Bool.not(Idle.own(at, slot))),
      Bool.or(
        Idle.stray(kids,
          Bool.pick(Idle.At, Bool.and(_, String.eq(t, name)), Idle.AArg{0n},
            Idle.inner(Idle.past(Lex.is_comma(k), at), slot)), slot, nm, name),
        Idle.stray(rest, Idle.past(Lex.is_comma(k), at), slot, nm, name)))
    == Bool.or(Bool.and(Idle.reads(k, t, nm), Bool.not(Idle.own(at, slot))),
      Bool.or(Idle.stray(kids, Idle.inner(Idle.past(Lex.is_comma(k), at), slot), slot, nm, name),
        Idle.stray(rest, Idle.past(Lex.is_comma(k), at), slot, nm, name))) : Bool}
  {==}

def Laws.stray_comma_starts_next_argument(_t, _l, _c, _tok, _rest, _place, _slot, _nm, _name):
  {==}

def Laws.stray_walks_bare_group(_open, _kids, _cl, _rest, _at, _slot, _nm, _name):
  {==}

def Laws.stray_walks_statement(_sk, _kids, _body, _at, _slot, _nm, _name):
  {==}

# a number compares equal to itself
law idle.cmp_refl:
  for n: Nat
  {Nat.cmp(n, n) == EQ{} : Cmp}

def idle.cmp_refl(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      idle.cmp_refl(p)

def Laws.own_argument_at_its_place(slot):
  s = Equal.sym(Cmp, Nat.cmp(slot, slot), EQ{}, idle.cmp_refl(slot))
  %s : {Cmp.is_eq(_) == True{} : Bool}
  {==}

def Laws.own_argument_nowhere_else(_place, _slot, e):
  e

def Laws.past_comma_moves_on(_place):
  {==}

# what the walk keeps going into a node is in the own argument exactly when
# the test it was made from held
law idle.pick_own:
  for b: Bool
  for slot: Nat
  {Idle.own(Bool.pick(Idle.At, b, Idle.AOwn{}, Idle.AOut{}), slot) == b : Bool}

def idle.pick_own(b, _slot):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.inner_keeps_own(at, slot):
  match at:
    case Idle.AOut{}:
      {==}
    case Idle.AOwn{}:
      {==}
    case Idle.AArg{place}:
      idle.pick_own(Nat.is_eq(place, slot), slot)

# what the walk keeps going into a node has no place to move on from
law idle.pick_next:
  for b: Bool
  for comma: Bool
  {Idle.past(comma, Bool.pick(Idle.At, b, Idle.AOwn{}, Idle.AOut{}))
    == Bool.pick(Idle.At, b, Idle.AOwn{}, Idle.AOut{}) : Idle.At}

def idle.pick_next(b, comma):
  match b:
    case True{}:
      match comma:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      match comma:
        case True{}:
          {==}
        case False{}:
          {==}

def Laws.inner_ignores_commas(at, slot, comma):
  idle.pick_next(Idle.own(at, slot), comma)
