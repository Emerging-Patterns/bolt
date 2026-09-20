# rule tail: a def that walks a list or a string (its first live parameter,
# the one a self-call shrinks) calls itself where the call is not the whole
# statement: `h <> go(t)`, `(1 + go(t) : U32)`, `+rest = go(t)`. Each such
# call holds a frame until the rest of the input is done, and the JS lane
# overflows its stack at a few thousand to ~64K elements (bend-http on a 48KB
# header, agora at ~4,900 entries); native is fine. Carry an accumulator and
# make the self-call the whole statement (reverse once at the end if order
# matters). Idiomatic code does this on purpose, so the rule is noisy: off
# unless asked. Self-calls inside a `Bool.pick` are left to the pick rule;
# laws and proofs are exempt.
import Base
import ../../src.bend as Src
import ../../finding.bend as F
import ../../../syntax/lex.bend as Lex
import ../../../syntax/tree.bend as Tree
import ../../../lazy/lazy.bend as Lazy
import ../calls.bend as Calls

# is a statement's chain exactly a call of the name, `name(..)`?
def bare(kids: Tree.Node, +name: String) -> Bool:
  match kids:
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, +t, l, c}}, Tree.NCons{g, Tree.NNil{}}}:
      Bool.and(String.eq(t, name), Tree.opens(g, "("))
    case other:
      False{}

# the self-calls not in tail position; skip: the chain is a bare self-call
def walk(n: Tree.Node, +name: String, +path: String, skip: Bool) -> List<&2, F.Finding>:
  match n:
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, +t, +l, +c}}, Tree.NCons{Tree.Group{Lex.Tok{_, +o, _, _}, +kids, _}, rest}}:
      +call = String.eq(o, "(")
      +me = Bool.and(Bool.and(call, String.eq(t, name)), Bool.not(skip))
      +inside = walk(kids, name, path, False{})
      +more = List.concat(&2, F.Finding, [
        Bool.pick(List<&2, F.Finding>, Bool.and(call, String.eq(t, "Bool.pick")), [], inside),
        walk(rest, name, path, False{})])
      Bool.pick(List<&2, F.Finding>, me,
        F.Finding{path, l, c, U32.from_nat(String.length(name)), "tail",
          name ++ " is not a tail call here; on a long list/string the JS lane overflows its stack; carry an accumulator"}
          <> more,
        more)
    case Tree.NCons{Tree.Group{open, kids, close}, rest}:
      List.concat(&2, F.Finding, [walk(kids, name, path, False{}), walk(rest, name, path, False{})])
    case Tree.NCons{Tree.Stmt{kind, +kids, body}, rest}:
      List.concat(&2, F.Finding, [walk(kids, name, path, bare(kids, name)), walk(body, name, path, False{}),
        walk(rest, name, path, False{})])
    case Tree.NCons{h, rest}:
      walk(rest, name, path, False{})
    case other:
      Nil{}

def check.go(ds: List<&2, Calls.Def>, +path: String, acc: List<&2, List<&2, F.Finding>>) -> List<&2, F.Finding>:
  match ds:
    case Nil{}:
      List.concat(&2, F.Finding, List.reverse(&2, List<&2, F.Finding>, acc))
    case Con{Calls.Def{+name, +sig, body}, rest}:
      check.go(rest, path,
        Lazy.stop(List<&2, F.Finding>, Bool.not(Bool.and(Calls.seq(sig), Bool.not(Calls.exempt(path, sig)))), [],
          _u => walk(body, name, path, False{})) <> acc)

# the rule
def check(s: Src.Src) -> List<&2, F.Finding>:
  Src.Src{path, text, toks, tree, bound, items} = s
  check.go(Calls.defs(tree), path, [])
