# rule strict: a def calls itself inside an operand of `Bool.and(..)` or
# `Bool.or(..)`, or in a comma-separated stretch holding `&&` or `||` (either
# side of the operator), matched by that exact text
# (a qualified `Base.Bool.or` is not seen). They are functions, not
# short-circuits: both sides always run (timed: `False{} && f(x)` costs all of
# f), so `ok(h) && go(rest)` walks the whole input after the answer is known,
# and the pending operator keeps a frame per step (the JS lane overflowed at
# ~64K this way). Match on the Bool in a helper, or carry it as an argument:
# `go(rest, ok(h))`. A self-call bound by a let above is not flagged: binding
# it says both run. Nor is one in a lambda body (`_u => go(rest)`, as
# `Lazy.or_else` takes): a thunk does not run eagerly, unless the body itself
# holds `&&` or `||`. A `=>` ends the stretch on its left, so a body's `&&` or
# `||` never reaches back past it: `go(x) <> _u => a && b` is not flagged.
import Base
import ../../src.bend as Src
import ../../finding.bend as F
import ../../../syntax/lex.bend as Lex
import ../../../syntax/tree.bend as Tree
import ../calls.bend as Calls
import ../../../lazy/lazy.bend as Lazy

# is the operator `&&` or `||`?
def logic(+tt: String) -> Bool:
  Bool.or(String.eq(tt, "&&"), String.eq(tt, "||"))

# does the chain, up to its first top-level comma or `=>`, hold `&&` or `||`?
def seg_op(nn: Tree.Node) -> Bool:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TComma{}, t, l, c}}, rest}:
      False{}
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TLam{}, t, l, c}}, rest}:
      False{}
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TOp{}, +t, l, c}}, rest}:
      +more = seg_op(rest)
      Bool.or(logic(t), more)
    case Tree.NCons{h, rest}:
      seg_op(rest)
    case other:
      False{}

# is the group after a name an operand: the stretch is hot, or it is the `(`
# of `Bool.and` or `Bool.or`
def inner(+hot: Bool, +oo: String, +tt: String) -> Bool:
  Bool.or(hot, Bool.and(String.eq(oo, "("), Bool.or(String.eq(tt, "Bool.and"), String.eq(tt, "Bool.or"))))

# a name, then a group: a finding when the name is the def, the group a `(`
# call and the stretch hot, then what the group and the rest report
def call(
  +tt: String,
  +ll: U32,
  +cc: U32,
  +oo: String,
  +name: String,
  +path: String,
  +hot: Bool,
  kids: List<&2, F.Finding>,
  rest: List<&2, F.Finding>
) -> List<&2, F.Finding>:
  +more = List.concat(&2, F.Finding, [kids, rest])
  Bool.pick(List<&2, F.Finding>, Bool.and(Bool.and(String.eq(oo, "("), String.eq(tt, name)), hot),
    F.Finding{path, ll, cc, U32.from_nat(String.length(name)), "strict",
      name ++ " recurses inside Bool.and or Bool.or, so both sides always run and there is no short-circuit; bind the call above."} <> more,
    more)

# a leaf read by its kind: past a comma, past a `=>`, or past any other
# token; only the branch taken runs
def leaf(
  kk: Lex.TokKind,
  comma: Unit -> List<&2, F.Finding>,
  lam: Unit -> List<&2, F.Finding>,
  plain: Unit -> List<&2, F.Finding>
) -> List<&2, F.Finding>:
  match kk:
    case Lex.TComma{}:
      comma(Unit{})
    case Lex.TLam{}:
      lam(Unit{})
    case _k:
      plain(Unit{})

# the self-calls in operands: outer is whether the enclosing group is an
# operand, hot whether the current comma segment is; a `=>` starts a lambda
# body, hot only by its own `&&`/`||`. A leaf is read by its kind in `leaf`,
# once the cell after it is known
def walk(nn: Tree.Node, +name: String, +path: String, +outer: Bool, +hot: Bool) -> List<&2, F.Finding>:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, +t, +l, +c}}, +rest}:
      match rest:
        case Tree.NCons{Tree.Group{Lex.Tok{_, +o, _, _}, +kids, _}, r2}:
          leaf(k, _u => walk(rest, name, path, outer, Bool.or(outer, seg_op(rest))),
            _v => walk(rest, name, path, outer, seg_op(rest)),
            _w => call(t, l, c, o, name, path, hot,
              walk(kids, name, path, inner(hot, o, t), Bool.or(inner(hot, o, t), seg_op(kids))),
              walk(r2, name, path, outer, hot)))
        case _r:
          leaf(k, _u => walk(rest, name, path, outer, Bool.or(outer, seg_op(rest))),
            _v => walk(rest, name, path, outer, seg_op(rest)), _w => walk(rest, name, path, outer, hot))
    case Tree.NCons{Tree.Group{open, +kids, close}, rest}:
      List.concat(&2, F.Finding, [walk(kids, name, path, hot, Bool.or(hot, seg_op(kids))),
        walk(rest, name, path, outer, hot)])
    case Tree.NCons{Tree.Stmt{kind, +kids, body}, rest}:
      List.concat(&2, F.Finding, [walk(kids, name, path, False{}, seg_op(kids)),
        walk(body, name, path, False{}, False{}),
        walk(rest, name, path, outer, hot)])
    case Tree.NCons{h, rest}:
      walk(rest, name, path, outer, hot)
    case other:
      Nil{}

def check.go(ds: List<&2, Calls.Def>, +path: String, acc: List<&2, List<&2, F.Finding>>) -> List<&2, F.Finding>:
  match ds:
    case Nil{}:
      List.concat(&2, F.Finding, List.reverse(&2, List<&2, F.Finding>, acc))
    case Con{Calls.Def{+name, +sig, body}, rest}:
      check.go(rest, path,
        Lazy.stop(List<&2, F.Finding>, Calls.exempt(path, sig), [],
          _u => walk(body, name, path, False{}, False{})) <> acc)

# the rule
def check(ss: Src.Src) -> List<&2, F.Finding>:
  Src.Src{path, text, toks, tree, bound, items} = ss
  check.go(Calls.defs(tree), path, [])
