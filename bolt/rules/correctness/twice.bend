# rule twice: a list pattern in a def that calls itself, opening with the
# same literal twice (`case 10 <> 10 <> _:`, `case Con{'a', Con{'a', t}}:`).
# The checker hangs on it (pi-bend BEND-018, b6a83a52; bend 2.0.16 still
# does). Only the opening pair was seen to hang: `10 <> 11 <> 10`,
# `_ <> 10 <> 10` and `10 <> 11 <> 11` check at once, and so does the same
# pattern in a def that does not recurse. Match one element per step, with a
# state. A def recurses when its body calls it, `name(..)`: a parameter or a
# value named like the def is not a call. Only a case's first match column is
# read: a list pattern in a later column of `match a b:` is not.
import Base
import ../../src.bend as Src
import ../../finding.bend as F
import ../../../syntax/lex.bend as Lex
import ../../../syntax/tree.bend as Tree
import ../../../syntax/bind.bend as Bind
import ../../../lazy/lazy.bend as Lazy
import ../tokens.bend as T
import ../calls.bend as Calls

# the literal a list pattern opens with: `x <> ..` or `Con{x, ..}`
def head(pat: Tree.Node) -> Maybe<&2, Lex.Tok>:
  match pat:
    case Tree.NCons{Tree.Leaf{Lex.Tok{+k, +t, l, c}}, Tree.NCons{Tree.Leaf{Lex.Tok{k2, +o, l2, c2}}, rest}}:
      Bool.pick(Maybe<&2, Lex.Tok>, Bool.and(T.is_lit(k), String.eq(o, "<>")), Some{Lex.Tok{k, t, l, c}}, None{})
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TUpper{}, +t, l, c}},
        Tree.NCons{Tree.Group{open, Tree.NCons{Tree.Leaf{Lex.Tok{+k, +x, l2, c2}}, kids}, close}, rest}}:
      Bool.pick(Maybe<&2, Lex.Tok>, Bool.and(String.eq(t, "Con"), T.is_lit(k)), Some{Lex.Tok{k, x, l2, c2}}, None{})
    case other:
      None{}

# the rest of a list pattern after its first element
def tail(pat: Tree.Node) -> Tree.Node:
  match pat:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TUpper{}, t, l, c}},
        Tree.NCons{Tree.Group{open, Tree.NCons{x, Tree.NCons{comma, kids}}, close}, rest}}:
      kids
    case Tree.NCons{x, Tree.NCons{op, rest}}:
      rest
    case other:
      Tree.NNil{}

# a finding at the second literal when it repeats the first
def same(aa: Maybe<&2, Lex.Tok>, bb: Maybe<&2, Lex.Tok>, +path: String) -> List<&2, F.Finding>:
  match aa bb:
    case Some{Lex.Tok{k, +t, l, c}} Some{Lex.Tok{k2, +t2, l2, c2}}:
      Bool.pick(List<&2, F.Finding>, String.eq(t, t2),
        [F.Finding{path, l2, c2, T.width(t2), "twice",
          "The same literal appears twice in one list pattern, which hangs the checker; match one element per step."}],
        [])
    case a2 b2:
      []

# a case statement's pattern, checked
def arm(+pat: Tree.Node, +path: String) -> List<&2, F.Finding>:
  same(head(pat), head(tail(pat)), path)

# every case statement under a recursive def, at any depth
def walk(nn: Tree.Node, +path: String) -> List<&2, F.Finding>:
  match nn:
    case Tree.NCons{Tree.Stmt{Tree.SCase{}, kids, body}, rest}:
      List.concat(&2, F.Finding, [arm(T.pattern(kids), path), walk(body, path), walk(rest, path)])
    case Tree.NCons{Tree.Stmt{kind, kids, body}, rest}:
      List.append(&2, F.Finding, walk(body, path), walk(rest, path))
    case Tree.NCons{h, rest}:
      walk(rest, path)
    case other:
      Nil{}

# a def's body, when it calls itself
def check.def(mm: Maybe<&2, String>, +body: Tree.Node, path: String) -> List<&2, F.Finding>:
  match mm:
    case None{}:
      Nil{}
    case Some{+name}:
      Lazy.stop(List<&2, F.Finding>, Bool.not(Calls.calls(body, name)), [], _u => walk(body, path))

def check.go(root: Tree.Node, +path: String) -> List<&2, F.Finding>:
  match root:
    case Tree.NCons{Tree.Stmt{Tree.SDef{}, +kids, body}, rest}:
      List.append(&2, F.Finding, check.def(Bind.declared(kids), body, path), check.go(rest, path))
    case Tree.NCons{h, rest}:
      check.go(rest, path)
    case other:
      Nil{}

# the rule
def check(ss: Src.Src) -> List<&2, F.Finding>:
  Src.Src{path, text, toks, tree, bound, items} = ss
  check.go(tree, path)
