# rule unused: a name bound by a let, a do-bind, a lambda, or as a parameter
# is never used. Pattern binders are exempt: naming every field of
# `Tok{k, t, l, c}` reads better than `_`. So are names starting with `_`,
# erased parameters (`-x`), which exist to be unused, a law's `for` names
# (hypotheses the proof takes by position), and every parameter of a foreign
# def (one whose body starts with `import`), which its C and JS bodies read,
# however its header is wrapped.
import Base
import ../../src.bend as Src
import ../../../lazy/lazy.bend as Lazy
import ../../finding.bend as F
import ../../../syntax/bind.bend as Bind
import ../../../syntax/tree.bend as Tree
import ../../../syntax/lex.bend as Lex

# the lines of these tokens, onto acc
def lines(ts: List<&2, Lex.Tok>, acc: List<&2, U32>) -> List<&2, U32>:
  match ts:
    case Nil{}:
      acc
    case Con{Lex.Tok{k, t, l, c}, rest}:
      l <> lines(rest, acc)

# every header line of the defs whose body is `import "./x.c"`, however the
# header is wrapped
def foreign(root: Tree.Node) -> List<&2, U32>:
  match root:
    case Tree.NCons{Tree.Stmt{Tree.SDef{}, kids, Tree.NCons{Tree.Stmt{Tree.SImport{}, ik, ib}, more}}, rest}:
      lines(Tree.leaves(kids), foreign(rest))
    case Tree.NCons{other, rest}:
      foreign(rest)
    case other:
      Nil{}

# does a binder of this kind count? Erased and foreign parameters do not
def reportable(kk: Bind.BindKind, +note: String, +line: U32, +foreign_lines: List<&2, U32>) -> Bool:
  match kk:
    case Bind.KLocal{}:
      True{}
    case Bind.KParam{}:
      Bool.and(Bool.not(String.starts_with(note, "-")), Bool.not(List.contains(~U32, ~U32.is_eq, foreign_lines, line)))
    case other:
      False{}

# is the binder at (line, col) the target of any use?
def used(uses: List<&2, Bind.Use>, +line: U32, +col: U32) -> Bool:
  match uses:
    case Nil{}:
      False{}
    case Con{Bind.Use{n, l, c, Bind.TLocal{+tl, +tc}}, rest}:
      Lazy.or_else(Bool.and(U32.is_eq(tl, line), U32.is_eq(tc, col)), _u => used(rest, line, col))
    case Con{other, rest}:
      used(rest, line, col)

# a binder's kind, for the message
def what(kk: Bind.BindKind) -> String:
  match kk:
    case Bind.KParam{}:
      "Parameter"
    case other:
      "Local"

def check.go(
  binds: List<&2, Bind.Bind>,
  +uses: List<&2, Bind.Use>,
  +fl: List<&2, U32>,
  +path: String
) -> List<&2, F.Finding>:
  match binds:
    case Nil{}:
      Nil{}
    case Con{Bind.Bind{+name, +line, +col, +kind, note}, rest}:
      +more = check.go(rest, uses, fl, path)
      +hit = Bool.and(reportable(kind, note, line, fl), Bool.not(String.starts_with(name, "_")))
      Bool.pick(List<&2, F.Finding>, Bool.and(hit, Bool.not(used(uses, line, col))),
        F.Finding{path, line, col, U32.from_nat(String.length(name)), "unused",
          what(kind) ++ " " ++ name ++ " is never used."} <> more, more)

def check.on(bb: Bind.Bound, fl: List<&2, U32>, path: String) -> List<&2, F.Finding>:
  Bind.Bound{binds, uses, scopes} = bb
  check.go(binds, uses, fl, path)

# the rule
def check(ss: Src.Src) -> List<&2, F.Finding>:
  Src.Src{path, text, toks, tree, bound, items} = ss
  check.on(bound, foreign(tree), path)
