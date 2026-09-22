# rule closed: a law in a LAWS.bend with no `for`/`exs` and no equality.
# A closed equality (`{lhs == rhs : T}`, including `IO(T)`) is a stated
# claim; the checker proves it by computing both sides. A law that is
# neither quantified nor an equality is this rule's finding. Laws outside
# LAWS.bend are not held to it.
import Base
import ../../src.bend as Src
import ../../finding.bend as F
import ../../../syntax/tree.bend as Tree
import ../../../syntax/lex.bend as Lex
import ../../../lazy/lazy.bend as Lazy
import ../../../syntax/bind.bend as Bind

# does a law's body bind anything (a `for` or `exs` line)?
def binds(body: Tree.Node) -> Bool:
  match body:
    case Tree.NCons{Tree.Stmt{Tree.SFor{}, kids, b}, rest}:
      True{}
    case Tree.NCons{h, rest}:
      binds(rest)
    case other:
      False{}

# is this node, or something under it, an `==`?
def has_eq(nn: Tree.Node) -> Bool:
  match nn:
    case Tree.Leaf{Lex.Tok{k, t, l, c}}:
      String.eq(t, "==")
    case Tree.Group{open, kids, close}:
      has_eq(kids)
    case Tree.Stmt{kind, kids, body}:
      Lazy.or_else(has_eq(kids), _u => has_eq(body))
    case Tree.NCons{h, rest}:
      Lazy.or_else(has_eq(h), _u => has_eq(rest))
    case other:
      False{}

# a law's name, `?` when it has none
def name.of(mm: Maybe<&2, String>) -> String:
  match mm:
    case None{}:
      "?"
    case Some{n}:
      n

def check.go(root: Tree.Node, +path: String) -> List<&2, F.Finding>:
  match root:
    case Tree.NCons{Tree.Stmt{Tree.SLaw{}, +kids, +body}, rest}:
      +more = check.go(rest, path)
      Lazy.stop(List<&2, F.Finding>,
        Lazy.or_else(binds(body), _u => Lazy.or_else(has_eq(kids), _u => has_eq(body))), more,
        _u => F.Finding{path, Tree.line(kids), Tree.col(kids), 0, "closed",
          "Law " ++ name.of(Bind.declared(kids))
            ++ " has no for and is not an equality; state {lhs == rhs : T}, including IO(T)."} <> more)
    case Tree.NCons{h, rest}:
      check.go(rest, path)
    case other:
      Nil{}

# the rule
def check(ss: Src.Src) -> List<&2, F.Finding>:
  Src.Src{+path, text, toks, tree, bound, items} = ss
  Lazy.stop(List<&2, F.Finding>, Bool.not(String.ends_with(path, "LAWS.bend")), [], _u => check.go(tree, path))
