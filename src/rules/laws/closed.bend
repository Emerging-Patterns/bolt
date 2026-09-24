# rule closed: a law in a LAWS.bend with no `for`/`exs` binder. A law with no
# binder holds for the one input it names, which makes it a unit test the
# checker runs, not a guarantee, and that is so for an equality (`{lhs == rhs
# : T}`, including `IO(T)`) as much as for anything else. Nothing exempts a
# closed law: quantify it, or delete it. Laws outside LAWS.bend are not held
# to it.
import Base
import ../../paths.bend as Paths
import ../../src.bend as Src
import ../../finding.bend as F
import ../../syntax/tree.bend as Tree
import ../../lazy/lazy.bend as Lazy
import ../../syntax/bind.bend as Bind

# does a law's body bind anything (a `for` or `exs` line)?
def binds(body: Tree.Node) -> Bool:
  match body:
    case Tree.NCons{Tree.Stmt{Tree.SFor{}, kids, b}, rest}:
      True{}
    case Tree.NCons{h, rest}:
      binds(rest)
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
      Lazy.stop(List<&2, F.Finding>, binds(body), more,
        _u => F.Finding{path, Tree.line(kids), Tree.col(kids), 0, "closed",
          "Law " ++ name.of(Bind.declared(kids))
            ++ " has no `for` or `exs` binder, so it checks a single case; quantify it or delete it."} <> more)
    case Tree.NCons{h, rest}:
      check.go(rest, path)
    case other:
      Nil{}

# the rule
def check(ss: Src.Src) -> List<&2, F.Finding>:
  Src.Src{+path, text, toks, tree, bound, items} = ss
  Lazy.stop(List<&2, F.Finding>, Bool.not(Paths.is_laws(path)), [], _u => check.go(tree, path))
