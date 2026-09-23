# rule snoc: `List.append(.., xs, [y])`, a list grown by one cell at its end.
# A List is a cons list, so the append copies every cell of xs to add one:
# in a loop that is quadratic, and even once it is a whole copy for one
# cell. Prepend (`y <> xs`) and reverse once when order matters, or build
# with `h <> go(t)`. A finding is a `List.append` token right before a `(`
# group whose last argument, split at the group's top-level commas, is a
# `[` group alone that holds something and no top-level comma. Any other
# last argument is left alone: `[]`, `[a, b]`, a `[y]` with more after it
# in the argument, a name bound to `[y]` by a let. `xs ++ [y]` is not
# seen, and does not check: `++` is `String.append`. concat (U004) reports
# the same append again when it is a self-call argument onto the parameter
# in its own slot. Laws and proofs do not run. The rule is opt-in: it is off
# unless a bolt.bend names `snoc` itself.
import Base
import ../../src.bend as Src
import ../../finding.bend as F
import ../../../syntax/lex.bend as Lex
import ../../../syntax/tree.bend as Tree
import ../calls.bend as Calls
import ../../../lazy/lazy.bend as Lazy

# the last argument; an empty chain when there is none
def last(as: List<&2, Tree.Node>) -> Tree.Node:
  match as:
    case Nil{}:
      Tree.NNil{}
    case Con{hd, Nil{}}:
      hd
    case Con{_hd, rest}:
      last(rest)

# exactly one argument, and it holds something
def one(as: List<&2, Tree.Node>) -> Bool:
  match as:
    case Con{Tree.NCons{_h, _t}, Nil{}}:
      True{}
    case other:
      False{}

# a list literal of one element alone: a `[` group holding something and no
# top-level comma, with nothing after it
def single(aa: Tree.Node) -> Bool:
  match aa:
    case Tree.NCons{Tree.Group{Lex.Tok{_, +o, _, _}, +kids, _}, Tree.NNil{}}:
      Bool.and(String.eq(o, "["), one(Calls.args(kids)))
    case other:
      False{}

# is the leaf's text and the group after it a List.append call onto a
# one-element list literal?
def grows(+tt: String, +oo: String, kids: Tree.Node) -> Bool:
  Bool.and(Bool.and(String.eq(tt, "List.append"), String.eq(oo, "(")), single(last(Calls.args(kids))))

# every List.append onto a one-element list literal, at any depth
def walk(nn: Tree.Node, +path: String) -> List<&2, F.Finding>:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, +t, l, c}}, Tree.NCons{Tree.Group{Lex.Tok{_, +o, _, _}, +kids, _}, rest}}:
      List.concat(&2, F.Finding, [
        Lazy.stop(List<&2, F.Finding>, Bool.not(grows(t, o, kids)), [],
          _u => [F.Finding{path, l, c, U32.from_nat(String.length(t)), "snoc",
            "List.append onto a one-element list copies the whole list to add one cell; prepend with <> and reverse once, or build with h <> go(t)."}]),
        walk(kids, path), walk(rest, path)])
    case Tree.NCons{Tree.Group{open, kids, close}, rest}:
      List.concat(&2, F.Finding, [walk(kids, path), walk(rest, path)])
    case Tree.NCons{Tree.Stmt{kind, kids, body}, rest}:
      List.concat(&2, F.Finding, [walk(kids, path), walk(body, path), walk(rest, path)])
    case Tree.NCons{h, rest}:
      walk(rest, path)
    case other:
      Nil{}

def check.go(ds: List<&2, Calls.Def>, +path: String, acc: List<&2, List<&2, F.Finding>>) -> List<&2, F.Finding>:
  match ds:
    case Nil{}:
      List.concat(&2, F.Finding, List.reverse(&2, List<&2, F.Finding>, acc))
    case Con{Calls.Def{_name, +sig, body}, rest}:
      check.go(rest, path,
        Lazy.stop(List<&2, F.Finding>, Calls.exempt(path, sig), [], _u => walk(body, path)) <> acc)

# the rule
def check(ss: Src.Src) -> List<&2, F.Finding>:
  Src.Src{path, text, toks, tree, bound, items} = ss
  check.go(Calls.defs(tree), path, [])
