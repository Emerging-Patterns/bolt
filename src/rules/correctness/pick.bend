# rule pick: a def calls itself in a branch of a `Bool.pick`. Bool.pick is a
# function, so both branches are evaluated whatever the condition. In both
# branches, two recursive calls a step is 2^n work where one was meant (a
# per-token scan that took 20 s this way took 20 ms as one pass): bind the
# call once above the pick (`+more = go(rest)`) and pick between `x <> more`
# and `more`. In one branch, the recursion runs even when the other branch
# was the answer: a search never stops early and walks the whole input
# (a lookup by key, a sorted insert). Match on the Bool instead,
# in a helper that takes it as a parameter. A self-call is the def's name
# followed by `(..)`: a parameter or a value named like the def is not one. A
# pick nested in a branch of one already reported is not reported again; one
# nested in its condition is. A
# search can hide the same bug by binding its recursion above the pick
# (`+more = go(rest)`, then `Bool.pick(T, hit, x, more)`): the walk still runs
# when the head is the answer (ez's `text.at`, native 8.81 s -> 4.15 s once it
# stopped). `search` reports that let, when the first statement after it in
# the same chain that reads the name is a pick alone that reads it only in
# its else branch: a filter, which reads it in both, is not a search. A
# do-bind, a let and a pick in different case arms, and a self-call that
# holds a pick on the same condition (which makes the call cheap on purpose)
# are left alone. The fix is to carry the test as a Bool into the next call
# and `match hit` first when the else branch is the bound name alone (a tail
# call), else a helper that matches on the condition; not a `Lazy` thunk,
# which stops early but leaves the loop on every step. rules.bend runs
# `check` and `search` both, as one rule. A
# law file, a proof file and a def that is a proof never run, so they are
# exempt: a def that returns a proof, or one written with no type at all
# (`def f(x, y):`), which fills the law named f.
import Base
import ../../src.bend as Src
import ../../finding.bend as F
import ../../syntax/lex.bend as Lex
import ../../syntax/tree.bend as Tree
import ../calls.bend as Calls
import ../../lazy/lazy.bend as Lazy

# do both branches (the third and fourth arguments) call the def?
def both(+as: List<&2, Tree.Node>, +name: String) -> Bool:
  Bool.and(Calls.calls(Calls.arg(as, 2n), name), Calls.calls(Calls.arg(as, 3n), name))

# does either branch call the def?
def once(+as: List<&2, Tree.Node>, +name: String) -> Bool:
  Bool.or(Calls.calls(Calls.arg(as, 2n), name), Calls.calls(Calls.arg(as, 3n), name))

# is argument nth of a group quiet: the group's own quiet, or, in a branch
# (the third or fourth argument) of a reported pick, hushed
def mute(+quiet: Bool, +hush: Bool, nth: Nat) -> Bool:
  match nth:
    case 0n:
      quiet
    case 1n:
      quiet
    case 2n:
      Bool.or(quiet, hush)
    case 3n:
      Bool.or(quiet, hush)
    case 4n+p:
      quiet

# the argument a token leaves the walk in: one further past a top-level comma
def next(k: Lex.TokKind, nth: Nat) -> Nat:
  match k:
    case Lex.TComma{}:
      1n+nth
    case other:
      nth

# every `Bool.pick(..)` in a chain, at any depth, that recurses in both
# branches or in one. The chain is argument nth of a group with quiet
# (inside a branch of a reported pick) and hush (the group is a reported
# pick, so its branches are quiet); a pick in the condition still counts.
def walk(nn: Tree.Node, +name: String, +path: String, +quiet: Bool, +hush: Bool, +nth: Nat) -> List<&2, F.Finding>:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, +t, +l, +c}}, Tree.NCons{Tree.Group{open, +kids, close}, rest}}:
      +at = next(k, nth)
      +q = mute(quiet, hush, at)
      +as = Calls.args(kids)
      +ispick = String.eq(t, "Bool.pick")
      +two = Bool.and(Bool.and(ispick, Bool.not(q)), both(as, name))
      +one = Bool.and(Bool.and(ispick, Bool.not(two)), Bool.and(Bool.not(q), once(as, name)))
      +more = List.concat(&2, F.Finding, [walk(kids, name, path, q, Bool.or(two, one), 0n),
        walk(rest, name, path, quiet, hush, at)])
      Bool.pick(List<&2, F.Finding>, two,
        F.Finding{path, l, c, 9, "pick",
          name ++ " calls itself in both branches of Bool.pick, which evaluates both, so both calls run; bind the call once above the pick."}
          <> more,
        Bool.pick(List<&2, F.Finding>, one,
          F.Finding{path, l, c, 9, "pick",
            name ++ " calls itself in one branch of Bool.pick, which evaluates both, so the call always runs and never exits early; branch with `match` on the condition instead."}
            <> more,
          more))
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}}, rest}:
      walk(rest, name, path, quiet, hush, next(k, nth))
    case Tree.NCons{Tree.Group{open, kids, close}, rest}:
      List.concat(&2, F.Finding, [walk(kids, name, path, mute(quiet, hush, nth), False{}, 0n),
        walk(rest, name, path, quiet, hush, nth)])
    case Tree.NCons{Tree.Stmt{kind, kids, body}, rest}:
      List.concat(&2, F.Finding, [walk(kids, name, path, mute(quiet, hush, nth), False{}, 0n),
        walk(body, name, path, mute(quiet, hush, nth), False{}, 0n), walk(rest, name, path, quiet, hush, nth)])
    case Tree.NCons{h, rest}:
      walk(rest, name, path, quiet, hush, nth)
    case other:
      Nil{}

# every reported pick in a chain walked at quiet, outside any pick's arguments
def picks(nn: Tree.Node, +name: String, +path: String, +quiet: Bool) -> List<&2, F.Finding>:
  walk(nn, name, path, quiet, False{}, 0n)

def check.go(ds: List<&2, Calls.Def>, +path: String, acc: List<&2, List<&2, F.Finding>>) -> List<&2, F.Finding>:
  match ds:
    case Nil{}:
      List.concat(&2, F.Finding, List.reverse(&2, List<&2, F.Finding>, acc))
    case Con{Calls.Def{+name, +sig, body}, rest}:
      check.go(rest, path,
        Lazy.stop(List<&2, F.Finding>, Calls.exempt(path, sig), [],
          _u => picks(body, name, path, False{})) <> acc)

# the rule
def check(s: Src.Src) -> List<&2, F.Finding>:
  Src.Src{path, text, toks, tree, bound, items} = s
  check.go(Calls.defs(tree), path, [])

# A search bound above its pick (laws/PickReportsBoundSearches.bend). In one
# chain of statements (a def's body, or one case arm's), a let `x = name(..)`
# or `+x = name(..)` of nothing but a self-call, and the first statement
# after it that reads x a `Bool.pick(..)` alone, whose condition and then
# branch do not read x and whose else branch does: a first-match search
# whose walk runs even when the head is the answer. A do-bind (`x <- ..`), a
# let and a pick in different arms, and a self-call that holds a
# `Bool.pick` on the pick's own condition (it makes the call cheap on
# purpose) are left alone.

# does a name leaf under the node spell x?
def search.reads(n: Tree.Node, +x: String) -> Bool:
  match n:
    case Tree.Leaf{Lex.Tok{k, +t, _l, _c}}:
      Bool.and(Lex.is_name(k), String.eq(t, x))
    case Tree.Group{_o, kids, _cl}:
      search.reads(kids, x)
    case Tree.Stmt{_k, kids, body}:
      +a = search.reads(kids, x)
      +b = search.reads(body, x)
      Bool.or(a, b)
    case Tree.NCons{h, t}:
      +a = search.reads(h, x)
      +b = search.reads(t, x)
      Bool.or(a, b)
    case Tree.NNil{}:
      False{}

# the node's tokens, each then a space (a group's open, not its close)
def search.text(n: Tree.Node) -> String:
  match n:
    case Tree.Leaf{Lex.Tok{_k, t, _l, _c}}:
      t ++ " "
    case Tree.Group{Lex.Tok{_k, o, _l, _c}, kids, _cl}:
      o ++ " " ++ search.text(kids)
    case Tree.Stmt{_k, kids, body}:
      +a = search.text(kids)
      +b = search.text(body)
      a ++ b
    case Tree.NCons{h, t}:
      +a = search.text(h)
      +b = search.text(t)
      a ++ b
    case Tree.NNil{}:
      ""

# does a `Bool.pick(..)` under the node, at any depth, have the condition
# whose text is cond?
def search.cheap(nn: Tree.Node, +cond: String) -> Bool:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{_k, +t, _l, _c}}, Tree.NCons{Tree.Group{Lex.Tok{_ko, +o, _lo, _co}, +kids, _cl},
      rest}}:
      +here = Bool.and(Bool.and(String.eq(t, "Bool.pick"), String.eq(o, "(")),
        String.eq(search.text(Calls.arg(Calls.args(kids), 1n)), cond))
      +a = search.cheap(kids, cond)
      +b = search.cheap(rest, cond)
      Bool.or(here, Bool.or(a, b))
    case Tree.Group{_o, kids, _cl}:
      search.cheap(kids, cond)
    case Tree.Stmt{_k, kids, body}:
      +a = search.cheap(kids, cond)
      +b = search.cheap(body, cond)
      Bool.or(a, b)
    case Tree.NCons{h, t}:
      +a = search.cheap(h, cond)
      +b = search.cheap(t, cond)
      Bool.or(a, b)
    case _other:
      False{}

# is the chain empty?
def search.empty(n: Tree.Node) -> Bool:
  match n:
    case Tree.NNil{}:
      True{}
    case _other:
      False{}

# is the chain the one name x alone?
def search.lone(n: Tree.Node, +x: String) -> Bool:
  match n:
    case Tree.NCons{Tree.Leaf{Lex.Tok{_k, +t, _l, _c}}, rest}:
      Bool.and(String.eq(t, x), search.empty(rest))
    case _other:
      False{}

# the finding at the bound self-call; tail: the else branch is the bound
# name alone, so the call can carry the test instead
def search.cite(+l: U32, +c: U32, +name: String, +path: String, tail: Bool) -> F.Finding:
  match tail:
    case True{}:
      F.Finding{path, l, c, U32.from_nat(String.length(name)), "pick",
        name ++ " binds its own call above a Bool.pick that reads it only in the else branch, so the walk runs even when the condition holds and the search never stops early; carry the test as a Bool into the next call (`go(rest, k, test(h))`) and `match hit` first, so the search stops and stays a loop."}
    case False{}:
      F.Finding{path, l, c, U32.from_nat(String.length(name)), "pick",
        name ++ " binds its own call above a Bool.pick that reads it only in the else branch, so the walk runs even when the condition holds and the search never stops early; branch with `match` on the condition in a helper that takes it as a parameter, so the call runs only in the branch that needs it."}

# the statement that reads the bound name first: a finding when it is a
# `Bool.pick(..)` alone that reads the name only in its else branch, and the
# self-call (its arguments args) holds no pick on the same condition
def search.judge(
  s: Tree.Node,
  +x: String,
  +args: Tree.Node,
  +l: U32,
  +c: U32,
  +name: String,
  +path: String
) -> List<&2, F.Finding>:
  match s:
    case Tree.Stmt{_k, Tree.NCons{Tree.Leaf{Lex.Tok{_kt, +t, _lt, _ct}}, Tree.NCons{Tree.Group{Lex.Tok{_ko, +o, _lo,
      _co}, +kids, _cl}, after}}, _body}:
      +as = Calls.args(kids)
      +cond = Calls.arg(as, 1n)
      +yes = Calls.arg(as, 2n)
      +no = Calls.arg(as, 3n)
      +shape = Bool.and(Bool.and(String.eq(t, "Bool.pick"), String.eq(o, "(")), search.empty(after))
      +only = Bool.and(Bool.not(Bool.or(search.reads(cond, x), search.reads(yes, x))), search.reads(no, x))
      Bool.pick(List<&2, F.Finding>,
        Bool.and(Bool.and(shape, only), Bool.not(search.cheap(args, search.text(cond)))),
        [search.cite(l, c, name, path, search.lone(no, x))], [])
    case _other:
      []

# the first statement of the chain that reads x, the chain's end (NNil)
# when none does; hit: prev, the one before the chain, did
def search.first(n: Tree.Node, +x: String, prev: Tree.Node, hit: Bool) -> Tree.Node:
  match n:
    case Tree.NCons{+h, t}:
      match hit:
        case True{}:
          prev
        case False{}:
          search.first(t, x, h, search.reads(h, x))
    case _other:
      match hit:
        case True{}:
          prev
        case False{}:
          Tree.NNil{}

# past the bound name, `=` and the callee (the token that names the call):
# a `(` group and nothing after it, and then the finding the first reader of
# the name gives
def search.call(
  kx: Lex.TokKind,
  +x: String,
  +e: String,
  callee: Lex.Tok,
  r3: Tree.Node,
  rest: Tree.Node,
  +name: String,
  +path: String
) -> List<&2, F.Finding>:
  Lex.Tok{_kn, +n, +l, +c} = callee
  match r3:
    case Tree.NCons{Tree.Group{Lex.Tok{_ko, +o, _lo, _co}, +args, _cl}, after}:
      +ok = Bool.and(Bool.and(Lex.is_name(kx), String.eq(e, "=")),
        Bool.and(Bool.and(String.eq(n, name), String.eq(o, "(")), search.empty(after)))
      Lazy.stop(List<&2, F.Finding>, Bool.not(ok), [],
        _u => search.judge(search.first(rest, x, Tree.NNil{}, False{}), x, args, l, c, name, path))
    case _other:
      []

# past the bound name and `=`: the leaf that names the call
def search.callee(
  kx: Lex.TokKind,
  +x: String,
  +e: String,
  r2: Tree.Node,
  rest: Tree.Node,
  +name: String,
  +path: String
) -> List<&2, F.Finding>:
  match r2:
    case Tree.NCons{Tree.Leaf{callee}, r3}:
      search.call(kx, x, e, callee, r3, rest, name, path)
    case _other:
      []

# past the bound name: the leaf that should be `=`
def search.eq(
  kx: Lex.TokKind,
  +x: String,
  r1: Tree.Node,
  rest: Tree.Node,
  +name: String,
  +path: String
) -> List<&2, F.Finding>:
  match r1:
    case Tree.NCons{Tree.Leaf{Lex.Tok{_ke, +e, _le, _ce}}, r2}:
      search.callee(kx, x, e, r2, rest, name, path)
    case _other:
      []

# a let's own tokens past any `+`: the leaf of the bound name
def search.bound(n: Tree.Node, rest: Tree.Node, +name: String, +path: String) -> List<&2, F.Finding>:
  match n:
    case Tree.NCons{Tree.Leaf{Lex.Tok{kx, +x, _lx, _cx}}, r1}:
      search.eq(kx, x, r1, rest, name, path)
    case _other:
      []

# a let's own tokens, a leading `+` skipped
def search.lead(kids: Tree.Node, rest: Tree.Node, +name: String, +path: String) -> List<&2, F.Finding>:
  match kids:
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, +t, l, c}}, +more}:
      search.bound(Bool.pick(Tree.Node, String.eq(t, "+"), more, Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}}, more}),
        rest, name, path)
    case _other:
      []

# a statement of the kind and own tokens, the chain after it rest: a let is
# read, anything else gives nothing
def search.stmt(
  kind: Tree.StmtKind,
  kids: Tree.Node,
  rest: Tree.Node,
  +name: String,
  +path: String
) -> List<&2, F.Finding>:
  match kind:
    case Tree.SLet{}:
      search.lead(kids, rest, name, path)
    case _other:
      []

# every search bound above its pick in a chain of statements and in the
# chains under them
def search.walk(n: Tree.Node, +name: String, +path: String) -> List<&2, F.Finding>:
  match n:
    case Tree.NCons{Tree.Stmt{kind, kids, body}, +rest}:
      List.concat(&2, F.Finding, [search.stmt(kind, kids, rest, name, path), search.walk(body, name, path),
        search.walk(rest, name, path)])
    case Tree.NCons{_h, rest}:
      search.walk(rest, name, path)
    case _other:
      Nil{}

def search.go(ds: List<&2, Calls.Def>, +path: String, acc: List<&2, List<&2, F.Finding>>) -> List<&2, F.Finding>:
  match ds:
    case Nil{}:
      List.concat(&2, F.Finding, List.reverse(&2, List<&2, F.Finding>, acc))
    case Con{Calls.Def{+name, +sig, body}, rest}:
      search.go(rest, path,
        Lazy.stop(List<&2, F.Finding>, Calls.exempt(path, sig), [], _u => search.walk(body, name, path)) <> acc)

# the rule's other half, run beside check: every search bound above its
# pick, def by def
def search(s: Src.Src) -> List<&2, F.Finding>:
  Src.Src{path, text, toks, tree, bound, items} = s
  search.go(Calls.defs(tree), path, [])
