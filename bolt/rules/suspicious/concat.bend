# rule concat: a def passes itself a parameter grown at the end, `p ++ x` or
# `List.append(.., p, ys)` (String.append(p, ..) too). A String and a List are
# cons lists, so appending copies all of p: the loop is quadratic, with right
# output (night-train's text step cost three times the render; rootagi's JSON
# stringify). Prepend (`x <> acc`) and reverse once at the end, build with
# `h <> go(t)`, or gather pieces and join them once.
import Base
import ../../src.bend as Src
import ../../finding.bend as F
import ../../../syntax/lex.bend as Lex
import ../../../syntax/tree.bend as Tree
import ../calls.bend as Calls
import ../../../lazy/lazy.bend as Lazy

# a chain that is exactly one lowercase name: its token
def lone(nn: Tree.Node) -> Maybe<&2, Lex.Tok>:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, t, l, c}}, Tree.NNil{}}:
      Some{Lex.Tok{Lex.TName{}, t, l, c}}
    case other:
      None{}

# the list a call appends onto: List.append's first list, String.append's first
def appended(+tt: String, as: List<&2, Tree.Node>) -> Maybe<&2, Lex.Tok>:
  +list = String.eq(tt, "List.append")
  +str = String.eq(tt, "String.append")
  Bool.pick(Maybe<&2, Lex.Tok>, Bool.or(list, str), lone(Calls.arg(as, Bool.pick(Nat, list, 2n, 0n))), None{})

# the name an argument appends onto, `p ++ ..` or an append call
def onto(aa: Tree.Node) -> Maybe<&2, Lex.Tok>:
  match aa:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, t, l, c}}, Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TOp{}, +o, _, _}}, _}}:
      Bool.pick(Maybe<&2, Lex.Tok>, String.eq(o, "++"), Some{Lex.Tok{Lex.TName{}, t, l, c}}, None{})
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, +t, l, c}}, Tree.NCons{Tree.Group{open, kids, close}, rest}}:
      appended(t, Calls.args(kids))
    case other:
      None{}

# a finding when the name is a parameter
def hit(
  mm: Maybe<&2, Lex.Tok>,
  +params: List<&2, String>,
  +path: String,
  +acc: List<&2, F.Finding>
) -> List<&2, F.Finding>:
  match mm:
    case None{}:
      acc
    case Some{Lex.Tok{k, +t, l, c}}:
      Bool.pick(List<&2, F.Finding>, List.contains(~String, ~String.eq, params, t),
        F.Finding{path, l, c, U32.from_nat(String.length(t)), "concat",
          t ++ " grows by appending on each step, which is quadratic; prepend and reverse once, or build with <>."} <> acc,
        acc)

# the findings on a self-call's arguments
def hits(
  as: List<&2, Tree.Node>,
  +params: List<&2, String>,
  +path: String,
  acc: List<&2, F.Finding>
) -> List<&2, F.Finding>:
  match as:
    case Nil{}:
      List.reverse(&2, F.Finding, acc)
    case Con{a, rest}:
      hits(rest, params, path, hit(onto(a), params, path, acc))

# every self-call's arguments
def walk(nn: Tree.Node, +name: String, +params: List<&2, String>, +path: String) -> List<&2, F.Finding>:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, +t, l, c}}, Tree.NCons{Tree.Group{Lex.Tok{_, +o, _, _}, +kids, _}, rest}}:
      +me = Bool.and(String.eq(o, "("), String.eq(t, name))
      List.concat(&2, F.Finding, [
        Lazy.stop(List<&2, F.Finding>, Bool.not(me), [], _u => hits(Calls.args(kids), params, path, [])),
        walk(kids, name, params, path), walk(rest, name, params, path)])
    case Tree.NCons{Tree.Group{open, kids, close}, rest}:
      List.concat(&2, F.Finding, [walk(kids, name, params, path), walk(rest, name, params, path)])
    case Tree.NCons{Tree.Stmt{kind, kids, body}, rest}:
      List.concat(&2, F.Finding, [walk(kids, name, params, path), walk(body, name, params, path),
        walk(rest, name, params, path)])
    case Tree.NCons{h, rest}:
      walk(rest, name, params, path)
    case other:
      Nil{}

def check.go(ds: List<&2, Calls.Def>, +path: String, acc: List<&2, List<&2, F.Finding>>) -> List<&2, F.Finding>:
  match ds:
    case Nil{}:
      List.concat(&2, F.Finding, List.reverse(&2, List<&2, F.Finding>, acc))
    case Con{Calls.Def{+name, +sig, body}, rest}:
      check.go(rest, path,
        Lazy.stop(List<&2, F.Finding>, Calls.exempt(path, sig), [],
          _u => walk(body, name, Calls.names(sig), path)) <> acc)

# the rule
def check(ss: Src.Src) -> List<&2, F.Finding>:
  Src.Src{path, text, toks, tree, bound, items} = ss
  check.go(Calls.defs(tree), path, [])
