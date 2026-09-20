# rule closed: a law in a LAWS.bend with no `for` or `exs` binder. It states
# one closed fact (`law sanity: {U32.add(2, 3) == 5 : U32}`), which the
# checker proves by computing it: a test, not a claim about every input, and
# a law cut down that way hides that the general one no longer holds. State
# it over a `for x: T` (or ask for an `exs` witness). Laws outside LAWS.bend
# are not held to it.
import Base
import ../../src.bend as Src
import ../../finding.bend as F
import ../../../syntax/tree.bend as Tree
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

# a law's name, `?` when it has none
def name.of(m: Maybe<&2, String>) -> String:
  match m:
    case None{}:
      "?"
    case Some{n}:
      n

def check.go(root: Tree.Node, +path: String) -> List<&2, F.Finding>:
  match root:
    case Tree.NCons{Tree.Stmt{Tree.SLaw{}, +kids, body}, rest}:
      +more = check.go(rest, path)
      Bool.pick(List<&2, F.Finding>, binds(body), more,
        F.Finding{path, Tree.line(kids), Tree.col(kids), 0, "closed", "law " ++ name.of(Bind.declared(kids))
          ++ " has no for: it is one computed case, not a claim about every input"} <> more)
    case Tree.NCons{h, rest}:
      check.go(rest, path)
    case other:
      Nil{}

# the rule
def check(s: Src.Src) -> List<&2, F.Finding>:
  Src.Src{+path, text, toks, tree, bound, items} = s
  Lazy.stop(List<&2, F.Finding>, Bool.not(String.ends_with(path, "LAWS.bend")), [], _u => check.go(tree, path))
