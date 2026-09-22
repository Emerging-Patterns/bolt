# rule quantify (opt-in): `closed`, strict. A law in a LAWS.bend with no
# `for`/`exs` binder, equality or not: a closed equality is a unit test the
# checker runs, and guarantees nothing past the one case it computes. No group
# turns it on; only `def quantify()` in a bolt.bend does (bolt/config.bend), so a
# project that does not name it sees nothing new. A closed law kept on purpose
# is exempt when the comment line right above its `law` line starts with
# `# toward ` (`# toward R-5`: what it leads to, in the project's own words);
# the finding says so, and nothing else exempts. Laws outside LAWS.bend are
# not held to it.
import Base
import ../../src.bend as Src
import ../../finding.bend as F
import ../../../syntax/tree.bend as Tree
import ../../../syntax/outline.bend as Outline
import ../../../lazy/lazy.bend as Lazy
import ../../../syntax/bind.bend as Bind
import ./closed.bend as Closed

# what the comment line right above a kept closed law starts with, its `# ` dropped
def marker() -> String:
  "toward "

# the last line of a comment block
def last.go(ls: List<&2, String>, +acc: String) -> String:
  match ls:
    case Nil{}:
      acc
    case Con{h, t}:
      last.go(t, h)

# the last line of a comment block, the one right above the item
def last(doc: String) -> String:
  last.go(String.lines(doc), "")

# is the law marked as kept closed?
def marked(doc: String) -> Bool:
  String.starts_with(last(doc), marker())

# the doc of the item on a line; the items are in line order, so the search
# stops at it (a LAWS.bend's items, once a law: cheap next to the parse)
def doc_at(items: List<&2, Outline.Item>, +at: U32) -> String:
  match items:
    case Nil{}:
      ""
    case Con{Outline.Item{kk, nn, +ln, sig, +doc, pp}, rest}:
      Lazy.stop(String, U32.is_le(at, ln), Bool.pick(String, U32.is_eq(ln, at), doc, ""), _u => doc_at(rest, at))

def check.go(root: Tree.Node, +items: List<&2, Outline.Item>, +path: String) -> List<&2, F.Finding>:
  match root:
    case Tree.NCons{Tree.Stmt{Tree.SLaw{}, +kids, body}, rest}:
      +at = Tree.line(kids)
      +more = check.go(rest, items, path)
      Lazy.stop(List<&2, F.Finding>, Lazy.or_else(Closed.binds(body), _u => marked(doc_at(items, at))), more,
        _u => F.Finding{path, at, Tree.col(kids), 0, "quantify",
          "Law " ++ Closed.name.of(Bind.declared(kids))
            ++ " has no for or exs, so it checks one case; quantify it, or mark a closed law kept on purpose with a"
            ++ " `# toward <goal>` line right above it."} <> more)
    case Tree.NCons{h, rest}:
      check.go(rest, items, path)
    case other:
      Nil{}

# the rule
def check(ss: Src.Src) -> List<&2, F.Finding>:
  Src.Src{+path, text, toks, tree, bound, items} = ss
  Lazy.stop(List<&2, F.Finding>, Bool.not(String.ends_with(path, "LAWS.bend")), [], _u => check.go(tree, items, path))
