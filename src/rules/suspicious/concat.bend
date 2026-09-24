# rule concat: a def passes itself a parameter grown at the end, `p ++ x` or
# `List.append(.., p, ys)` (String.append(p, ..) too), as the argument in p's
# own position, the slot it carries; p grown into another slot is not a
# finding. The argument is that append written in place, inside any number
# of parentheses (`(p ++ x)`), or a lone name read from a let: the nearest
# `q = ..` or `+q = ..` of that name before the call in its block or an
# enclosing one, whose right side is such an append (a later let of the name
# shadows it; other binders, a typed or destructuring let and a do-bind do
# not count). A String and a List are cons lists, so appending copies all of
# p: the loop is quadratic, with right output (night-train's text step cost
# three times the render; rootagi's JSON stringify). Prepend (`x <> acc`)
# and reverse once at the end, build with `h <> go(t)`, or gather pieces and
# join them once.
import Base
import ../../src.bend as Src
import ../../finding.bend as F
import ../../syntax/lex.bend as Lex
import ../../syntax/tree.bend as Tree
import ../calls.bend as Calls
import ../../lazy/lazy.bend as Lazy

# a leaf that is a lowercase name: its token. The rule matches a leaf's kind
# here and in bound.is_eq only; the rest reads kinds through these
def lone.name(nn: Tree.Node) -> Maybe<&2, Lex.Tok>:
  match nn:
    case Tree.Leaf{Lex.Tok{Lex.TName{}, t, l, c}}:
      Some{Lex.Tok{Lex.TName{}, t, l, c}}
    case other:
      None{}

# a chain that is exactly one lowercase name: its token
def lone(nn: Tree.Node) -> Maybe<&2, Lex.Tok>:
  match nn:
    case Tree.NCons{h, Tree.NNil{}}:
      lone.name(h)
    case other:
      None{}

# the list a call appends onto: List.append's first list, String.append's first
def appended(+tt: String, as: List<&2, Tree.Node>) -> Maybe<&2, Lex.Tok>:
  +list = String.eq(tt, "List.append")
  +str = String.eq(tt, "String.append")
  Bool.pick(Maybe<&2, Lex.Tok>, Bool.or(list, str), lone(Calls.arg(as, Bool.pick(Nat, list, 2n, 0n))), None{})

# a leaf, then a group: the call's append
def onto.call(hh: Tree.Node, kids: Tree.Node) -> Maybe<&2, Lex.Tok>:
  match hh:
    case Tree.Leaf{Lex.Tok{k, +t, l, c}}:
      appended(t, Calls.args(kids))
    case other:
      None{}

# a first cell, then the second: a name then `++`, or a call
def onto.next(+hh: Tree.Node, h2: Tree.Node) -> Maybe<&2, Lex.Tok>:
  match h2:
    case Tree.Leaf{Lex.Tok{k, +o, _l, _c}}:
      Bool.pick(Maybe<&2, Lex.Tok>, Bool.and(Calls.kind.oper(k), String.eq(o, "++")), lone.name(hh), None{})
    case Tree.Group{open, kids, close}:
      onto.call(hh, kids)
    case other:
      None{}

# the name an argument appends onto, `p ++ ..` or an append call, inside any
# number of parentheses
def onto(aa: Tree.Node) -> Maybe<&2, Lex.Tok>:
  match aa:
    case Tree.NCons{Tree.Group{Lex.Tok{_, +o, _, _}, kids, _}, Tree.NNil{}}:
      Lazy.stop(Maybe<&2, Lex.Tok>, Bool.not(String.eq(o, "(")), None{}, _u => onto(kids))
    case Tree.NCons{hh, Tree.NCons{h2, rest}}:
      onto.next(hh, h2)
    case other:
      None{}

# a let of one plain name in scope: the name, and what its right side
# appends onto
type Let is Data:
  Let{name: String, onto: Maybe<&2, Lex.Tok>}

# what the nearest let of the name appends onto; nothing when no let binds it
def find(lets: List<&2, Let>, +name: String) -> Maybe<&2, Lex.Tok>:
  match lets:
    case Nil{}:
      None{}
    case Con{Let{+nm, mm}, rest}:
      Lazy.stop(Maybe<&2, Lex.Tok>, String.eq(nm, name), mm, _u => find(rest, name))

# what the let of a lone name appends onto
def via.of(mm: Maybe<&2, Lex.Tok>, +lets: List<&2, Let>) -> Maybe<&2, Lex.Tok>:
  match mm:
    case None{}:
      None{}
    case Some{Lex.Tok{k, +t, l, c}}:
      find(lets, t)

# the name an argument appends onto, when it is a lone name read from a let
def via(aa: Tree.Node, +lets: List<&2, Let>) -> Maybe<&2, Lex.Tok>:
  via.of(lone(aa), lets)

# the first maybe when it holds a token, else the second
def either(aa: Maybe<&2, Lex.Tok>, bb: Maybe<&2, Lex.Tok>) -> Maybe<&2, Lex.Tok>:
  match aa:
    case None{}:
      bb
    case Some{tok}:
      Some{tok}

# the name an argument appends onto, in place or through a let
def seen(+aa: Tree.Node, +lets: List<&2, Let>) -> Maybe<&2, Lex.Tok>:
  either(onto(aa), via(aa, lets))

# an `=`
def bound.eq(kk: Lex.TokKind) -> Bool:
  match kk:
    case Lex.TEq{}:
      True{}
    case other:
      False{}

# a name, then `=`, then the right side: the let
def bound.of(mm: Maybe<&2, Lex.Tok>, +h2: Tree.Node, rhs: Tree.Node) -> Maybe<&2, Let>:
  match mm:
    case None{}:
      None{}
    case Some{Lex.Tok{k, +t, l, c}}:
      Lazy.stop(Maybe<&2, Let>, Bool.not(Calls.kind.leaf(~bound.eq, h2)), None{}, _u => Some{Let{t, onto(rhs)}})

# a plain name, then `=`, then the right side: the let
def bound.named(+hh: Tree.Node, +h2: Tree.Node, rhs: Tree.Node) -> Maybe<&2, Let>:
  bound.of(lone.name(hh), h2, rhs)

# `+`, then a plain name, `=` and the right side: the let
def bound.plus(+h1: Tree.Node, +h2: Tree.Node, rest: Tree.Node) -> Maybe<&2, Let>:
  match rest:
    case Tree.NCons{h3, rhs}:
      Lazy.stop(Maybe<&2, Let>, Bool.not(String.eq(Calls.leaf.text(h1), "+")), None{},
        _u => bound.named(h2, h3, rhs))
    case other:
      None{}

# the let a statement's own tokens make, when it binds one plain name with
# `=`, bare or `+`
def bound(kids: Tree.Node) -> Maybe<&2, Let>:
  match kids:
    case Tree.NCons{+h1, Tree.NCons{+h2, +rest}}:
      Lazy.either(Maybe<&2, Let>, Calls.kind.leaf(~Calls.kind.oper, h1), _u => bound.plus(h1, h2, rest),
        _v => bound.named(h1, h2, rest))
    case other:
      None{}

# the lets in scope after one more, when there is one
def push(mm: Maybe<&2, Let>, +lets: List<&2, Let>) -> List<&2, Let>:
  match mm:
    case None{}:
      lets
    case Some{lt}:
      lt <> lets

# a finding when the name is the parameter of the argument's own slot
def hit(
  mm: Maybe<&2, Lex.Tok>,
  +slot: String,
  +path: String,
  +acc: List<&2, F.Finding>
) -> List<&2, F.Finding>:
  match mm:
    case None{}:
      acc
    case Some{Lex.Tok{k, +t, l, c}}:
      Bool.pick(List<&2, F.Finding>, String.eq(t, slot),
        F.Finding{path, l, c, U32.from_nat(String.length(t)), "concat",
          t ++ " is appended to on every step, which copies it each time and makes the loop quadratic; prepend and reverse once at the end, or build with <>."} <> acc,
        acc)

# the findings on a self-call's arguments, each against the parameter in its
# position (params, from the argument's own slot on)
def hits(
  as: List<&2, Tree.Node>,
  +params: List<&2, String>,
  +lets: List<&2, Let>,
  +path: String,
  acc: List<&2, F.Finding>
) -> List<&2, F.Finding>:
  match as:
    case Nil{}:
      List.reverse(&2, F.Finding, acc)
    case Con{+a, rest}:
      +slot = Maybe.default(&2, String, List.head(&2, String, params), "")
      hits(rest, List.tail(&2, String, params), lets, path, hit(seen(a, lets), slot, path, acc))

# the lets a statement leaves in scope for the statements after it
def after(kind: Tree.StmtKind, +kids: Tree.Node, +lets: List<&2, Let>) -> List<&2, Let>:
  match kind:
    case Tree.SLet{}:
      push(bound(kids), lets)
    case other:
      lets

# every self-call's arguments, with the lets in scope
def walk(
  nn: Tree.Node,
  +name: String,
  +params: List<&2, String>,
  +lets: List<&2, Let>,
  +path: String
) -> List<&2, F.Finding>:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, +t, l, c}}, Tree.NCons{Tree.Group{Lex.Tok{_, +o, _, _}, +kids, _}, rest}}:
      +me = Bool.and(String.eq(o, "("), String.eq(t, name))
      List.concat(&2, F.Finding, [
        Lazy.stop(List<&2, F.Finding>, Bool.not(me), [], _u => hits(Calls.args(kids), params, lets, path, [])),
        walk(kids, name, params, lets, path), walk(rest, name, params, lets, path)])
    case Tree.NCons{Tree.Group{open, kids, close}, rest}:
      List.concat(&2, F.Finding, [walk(kids, name, params, lets, path), walk(rest, name, params, lets, path)])
    case Tree.NCons{Tree.Stmt{kind, +kids, body}, rest}:
      List.concat(&2, F.Finding, [walk(kids, name, params, lets, path), walk(body, name, params, lets, path),
        walk(rest, name, params, after(kind, kids, lets), path)])
    case Tree.NCons{h, rest}:
      walk(rest, name, params, lets, path)
    case other:
      Nil{}

def check.go(ds: List<&2, Calls.Def>, +path: String, acc: List<&2, List<&2, F.Finding>>) -> List<&2, F.Finding>:
  match ds:
    case Nil{}:
      List.concat(&2, F.Finding, List.reverse(&2, List<&2, F.Finding>, acc))
    case Con{Calls.Def{+name, +sig, body}, rest}:
      check.go(rest, path,
        Lazy.stop(List<&2, F.Finding>, Calls.exempt(path, sig), [],
          _u => walk(body, name, Calls.names(sig), [], path)) <> acc)

# the rule
def check(ss: Src.Src) -> List<&2, F.Finding>:
  Src.Src{path, text, toks, tree, bound, items} = ss
  check.go(Calls.defs(tree), path, [])
