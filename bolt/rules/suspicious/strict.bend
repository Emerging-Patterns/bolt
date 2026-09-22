# rule strict: a def calls itself inside an operand of `Bool.and(..)` or
# `Bool.or(..)`, or on either side of `&&` or `||`. They are functions, not
# short-circuits: both sides always run (timed: `False{} && f(x)` costs all of
# f), so `ok(h) && go(rest)` walks the whole input after the answer is known,
# and the pending operator keeps a frame per step (the JS lane overflowed at
# ~64K this way). Match on the Bool in a helper, or carry it as an argument:
# `go(rest, ok(h))`. A self-call bound by a let above is not flagged: binding
# it says both run.
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

# does the chain, up to its first top-level comma, hold `&&` or `||`?
def seg_op(nn: Tree.Node) -> Bool:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TComma{}, t, l, c}}, rest}:
      False{}
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TOp{}, +t, l, c}}, rest}:
      +more = seg_op(rest)
      Bool.or(logic(t), more)
    case Tree.NCons{h, rest}:
      seg_op(rest)
    case other:
      False{}

# the self-calls in operands: outer is whether the enclosing group is an
# operand, hot whether the current comma segment is
def walk(nn: Tree.Node, +name: String, +path: String, +outer: Bool, +hot: Bool) -> List<&2, F.Finding>:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TComma{}, t, l, c}}, +rest}:
      walk(rest, name, path, outer, Bool.or(outer, seg_op(rest)))
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, +t, +l, +c}}, Tree.NCons{Tree.Group{Lex.Tok{_, +o, _, _}, +kids, _}, rest}}:
      +call = String.eq(o, "(")
      +me = Bool.and(Bool.and(call, String.eq(t, name)), hot)
      +inner = Bool.or(hot, Bool.and(call, Bool.or(String.eq(t, "Bool.and"), String.eq(t, "Bool.or"))))
      +more = List.concat(&2, F.Finding, [walk(kids, name, path, inner, Bool.or(inner, seg_op(kids))),
        walk(rest, name, path, outer, hot)])
      Bool.pick(List<&2, F.Finding>, me,
        F.Finding{path, l, c, U32.from_nat(String.length(name)), "strict",
          name ++ " recurses inside Bool.and/or; both sides always run (no short-circuit)"} <> more,
        more)
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
