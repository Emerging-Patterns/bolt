# rule pick: a def calls itself in both branches of a `Bool.pick`. Bool.pick
# is a function, so both branches are evaluated whatever the condition: two
# recursive calls a step is 2^n work where one was meant (a per-token scan
# that took 20 s this way took 20 ms as one pass). Bind the call once above
# the pick (`+more = go(rest)`) and pick between `x <> more` and `more`.
import Base
import ../finding.bend as F
import ../../syntax/lex.bend as Lex
import ../../syntax/tree.bend as Tree
import ../../syntax/bind.bend as Bind

# the arguments of a group, split at its top-level commas (each a chain)
def args.go(kids: Tree.Node, cur: Tree.Node, acc: List<&2, Tree.Node>) -> List<&2, Tree.Node>:
  match kids:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TComma{}, t, l, c}}, rest}:
      args.go(rest, Tree.NNil{}, Tree.reverse(cur, Tree.NNil{}) <> acc)
    case Tree.NCons{h, rest}:
      args.go(rest, Tree.NCons{h, cur}, acc)
    case other:
      List.reverse(&2, Tree.Node, Tree.reverse(cur, Tree.NNil{}) <> acc)

# the arguments of a group
def args(kids: Tree.Node) -> List<&2, Tree.Node>:
  args.go(kids, Tree.NNil{}, [])

# the nth argument, or nothing
def arg(as: List<&2, Tree.Node>, n: Nat) -> Tree.Node:
  match as n:
    case Con{h, t} 0n:
      h
    case Con{h, t} 1n+p:
      arg(t, p)
    case Nil{} m:
      Tree.NNil{}

# does the name appear anywhere under the node?
def mentions(n: Tree.Node, +name: String) -> Bool:
  match n:
    case Tree.Leaf{Lex.Tok{k, +t, l, c}}:
      String.eq(t, name)
    case Tree.Group{open, kids, close}:
      mentions(kids, name)
    case Tree.Stmt{kind, kids, body}:
      Bool.or(mentions(kids, name), mentions(body, name))
    case Tree.NNil{}:
      False{}
    case Tree.NCons{h, t}:
      Bool.or(mentions(h, name), mentions(t, name))

# do both branches (the third and fourth arguments) name the def?
def both(kids: Tree.Node, +name: String) -> Bool:
  +as = args(kids)
  Bool.and(mentions(arg(as, 2n), name), mentions(arg(as, 3n), name))

# every `Bool.pick(..)` in a chain, at any depth, whose branches both recurse
def picks(n: Tree.Node, +name: String, +path: String) -> List<&2, F.Finding>:
  match n:
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, +t, +l, +c}}, Tree.NCons{Tree.Group{open, +kids, close}, rest}}:
      +more = List.concat(&2, F.Finding, [picks(kids, name, path), picks(rest, name, path)])
      Bool.pick(List<&2, F.Finding>, Bool.and(String.eq(t, "Bool.pick"), both(kids, name)),
        F.Finding{path, l, c, 9, "pick", name ++ " recurses in both branches; Bool.pick runs both"} <> more,
        more)
    case Tree.NCons{Tree.Group{open, kids, close}, rest}:
      List.concat(&2, F.Finding, [picks(kids, name, path), picks(rest, name, path)])
    case Tree.NCons{Tree.Stmt{kind, kids, body}, rest}:
      List.concat(&2, F.Finding, [picks(kids, name, path), picks(body, name, path), picks(rest, name, path)])
    case Tree.NCons{h, rest}:
      picks(rest, name, path)
    case other:
      Nil{}

# a def's body, against its name
def check.def(m: Maybe<&2, String>, body: Tree.Node, path: String) -> List<&2, F.Finding>:
  match m:
    case None{}:
      Nil{}
    case Some{name}:
      picks(body, name, path)

def check.go(root: Tree.Node, +path: String) -> List<&2, F.Finding>:
  match root:
    case Tree.NCons{Tree.Stmt{Tree.SDef{}, kids, body}, rest}:
      List.concat(&2, F.Finding, [check.def(Bind.declared(kids), body, path), check.go(rest, path)])
    case Tree.NCons{h, rest}:
      check.go(rest, path)
    case other:
      Nil{}

# the rule
def check(path: String, text: String) -> List<&2, F.Finding>:
  check.go(Tree.parse(text), path)
