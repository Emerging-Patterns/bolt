# `unused` reports exactly an unused let, do-bind, lambda binder or parameter,
# with the header's exemptions: a foreign def, whose parameters are exempt, is
# one whose body's first statement is `import`, wherever its header's `->` and
# return type fall (its body is what is under its whole header,
# laws/DefSignatureRunsToItsColon.bend).
#
# also rests on: laws/DefSignatureRunsToItsColon.bend
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/syntax/bind.bend as Bind
import ../src/src.bend as Src
import ../src/syntax/tree.bend as Tree
import ../src/syntax/outline.bend as Outline
import ../src/rules/tokens.bend as T
import ../src/rules/suspicious/unused.bend as Unused
import ../src/rules/calls.bend as Calls

# The binding rule, unused. It reads the binder's lists: every binder, and
# every use with what it resolves to. A binder counts when it is a let, a
# do-bind or a lambda binder (KLocal), or a parameter (KParam) that is not
# erased (its declaration opens with `-`) and does not sit on a header line
# of a foreign def (the first statement under its whole header, Calls.under,
# is an `import`); its name does not start with `_`; and no use resolves to
# its position. Pattern binders (KPat), a law's `for` names (KFor) and every
# other kind never count.

# is the statement an import?
def unused.is_import(sk: Tree.StmtKind) -> Bool:
  match sk:
    case Tree.SImport{}:
      True{}
    case other:
      False{}

# does a body open with an import statement?
def unused.opens(body: Tree.Node) -> Bool:
  match body:
    case Tree.NCons{Tree.Stmt{sk, kids, b}, rest}:
      unused.is_import(sk)
    case other:
      False{}

# does a def's body open with an import statement, wherever its header's `->`
# and return type fall? then the def is foreign
def unused.imported(kids: Tree.Node, body: Tree.Node) -> Bool:
  unused.opens(Calls.under(kids, body))

# the line of each token
def unused.token_lines(ts: List<&2, Lex.Tok>) -> List<&2, U32>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{Lex.Tok{k, t, +l, c}, rest}:
      l <> unused.token_lines(rest)

# every line a foreign def's header covers, however it is wrapped: the lines
# of its own tokens, def by def
def unused.headers(root: Tree.Node) -> List<&2, U32>:
  match root:
    case Tree.NCons{Tree.Stmt{Tree.SDef{}, +kids, body}, rest}:
      +more = unused.headers(rest)
      Bool.pick(List<&2, U32>, unused.imported(kids, body),
        List.append(&2, U32, unused.token_lines(Tree.leaves(kids)), more), more)
    case Tree.NCons{h, rest}:
      unused.headers(rest)
    case other:
      Nil{}

# does a use's target name the binder at (line, col)?
def unused.names(tg: Bind.Target, +line: U32, +col: U32) -> Bool:
  match tg:
    case Bind.TLocal{tl, tc}:
      Bool.and(U32.is_eq(tl, line), U32.is_eq(tc, col))
    case Bind.TItem{n}:
      False{}
    case Bind.TQual{a, n}:
      False{}
    case Bind.TFree{}:
      False{}

# does any use resolve to the binder at (line, col)?
def unused.seen(uses: List<&2, Bind.Use>, +line: U32, +col: U32) -> Bool:
  match uses:
    case Nil{}:
      False{}
    case Con{Bind.Use{n, l, c, tg}, rest}:
      Bool.or(unused.names(tg, line, col), unused.seen(rest, line, col))

# is a binder of this kind one the rule speaks for? A let, do-bind or lambda
# binder is; a parameter is unless erased or on a foreign header line;
# nothing else is
def unused.kept(kk: Bind.BindKind, +note: String, +line: U32, +fl: List<&2, U32>) -> Bool:
  match kk:
    case Bind.KItem{}:
      False{}
    case Bind.KCtor{}:
      False{}
    case Bind.KParam{}:
      Bool.and(Bool.not(String.starts_with(note, "-")), Bool.not(List.contains(~U32, ~U32.is_eq, fl, line)))
    case Bind.KTypeParam{}:
      False{}
    case Bind.KField{}:
      False{}
    case Bind.KLocal{}:
      True{}
    case Bind.KPat{}:
      False{}
    case Bind.KFor{}:
      False{}
    case Bind.KTypeVar{}:
      False{}

# how many binders count, are not named `_..`, and have no use
def unused.count(binds: List<&2, Bind.Bind>, +uses: List<&2, Bind.Use>, +fl: List<&2, U32>) -> Nat:
  match binds:
    case Nil{}:
      0n
    case Con{Bind.Bind{+name, +line, +col, kk, +note}, rest}:
      +m = unused.count(rest, uses, fl)
      Bool.pick(Nat, Bool.and(Bool.and(unused.kept(kk, note, line, fl), Bool.not(String.starts_with(name, "_"))),
        Bool.not(unused.seen(uses, line, col))), 1n+m, m)

# LAW: unused reports one finding for each let, do-bind, lambda binder or
# parameter no use resolves to, and none for any other binder: not a pattern
# binder, a name starting with `_`, an erased parameter, a law's `for` name,
# or a parameter of a foreign def (one whose body opens with `import`),
# wherever its header's `->` and return type fall
law unused_counts:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for +tree: Tree.Node
  for binds: List<&2, Bind.Bind>
  for +uses: List<&2, Bind.Use>
  for scopes: List<&2, Bind.Scope>
  for items: List<&2, Outline.Item>
  {List.length(&2, F.Finding, Unused.check(Src.Src{path, text, toks, tree, Bind.Bound{binds, uses, scopes}, items}))
    == unused.count(binds, uses, unused.headers(tree)) : Nat}
