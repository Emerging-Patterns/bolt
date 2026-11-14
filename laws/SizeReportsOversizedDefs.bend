# `arity`, `length` and `depth` each report exactly one finding for each def
# of a file that is not exempt (a law file, a proof file, a def that is a
# proof: src/rules/calls.bend's `exempt`) and whose measure is over the
# limit the rule is run at, and none for any other def; in a LAWS.bend or a
# PROOF.bend none at all, so told a file's role by its name each finds what
# it finds.
#
# The measures. arity counts a def's parameters that have a lowercase name
# of their own, so a type parameter is none. length reads the greatest line
# of a token of the def, each token taking the line over when its own is
# later. depth puts the statements under one that opens a block (a `:` among
# its own tokens) one level down, and those under one that does not (a line
# an expression wrapped onto) at the same level.
#
# Not proved here: that no comment or string changes a finding
# (laws/CodeRulesIgnoreCommentsAndStrings.bend does not list these rules
# yet; they read a def's tokens' kinds and lines, never a text but a
# parameter's name).
import Base
import ../src/finding.bend as F
import ../src/paths.bend as Paths
import ../src/role.bend as Role
import ../src/src.bend as Src
import ../src/syntax/lex.bend as Lex
import ../src/syntax/tree.bend as Tree
import ../src/syntax/bind.bend as Bind
import ../src/syntax/outline.bend as Outline
import ../src/rules/calls.bend as Calls
import ../src/rules/style/size.bend as Size

# is the def one the rule reports: not exempt, and over the limit?
def over(dim: Size.Dim, path: String, +sig: Tree.Node, body: Tree.Node, max: U32) -> Bool:
  Bool.and(Bool.not(Calls.exempt(path, sig)), U32.is_gt(Size.measure(dim, sig, body), max))

# how many of the defs the rule reports
def over_count(ds: List<&2, Calls.Def>, +dim: Size.Dim, +path: String, +max: U32) -> Nat:
  match ds:
    case Nil{}:
      0n
    case Con{Calls.Def{_name, sig, body}, rest}:
      +m = over_count(rest, dim, path, max)
      Bool.pick(Nat, over(dim, path, sig, body, max), 1n+m, m)

# LAW: over a file's defs, at any limit, each rule reports one finding for
# each def that is not exempt and whose measure is over the limit, and none
# for any other
law size_counts:
  for ds: List<&2, Calls.Def>
  for +dim: Size.Dim
  for +path: String
  for +max: U32
  {List.length(&2, F.Finding, Size.check.go(ds, dim, path, max)) == over_count(ds, dim, path, max) : Nat}

# LAW: each rule reports nothing in a LAWS.bend or a PROOF.bend, whatever
# the source holds
law size_exempt:
  for +dim: Size.Dim
  for +max: U32
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  for +e: {Paths.is_law_file(path) == True{} : Bool}
  {Size.check(dim, Src.Src{path, text, toks, tree, bound, items}, max) == Nil{} : List<&2, F.Finding>}

# LAW: each rule, which checks nothing in a law or proof file, told a file's
# role by its name finds what it finds
law role_size:
  for +dim: Size.Dim
  for +max: U32
  for +path: String
  for +text: String
  for +toks: List<&2, Lex.Tok>
  for +tree: Tree.Node
  for +bound: Bind.Bound
  for +items: List<&2, Outline.Item>
  {Role.skip(Role.of_path(path), _u => Size.check(dim, Src.Src{path, text, toks, tree, bound, items}, max))
    == Size.check(dim, Src.Src{path, text, toks, tree, bound, items}, max) : List<&2, F.Finding>}

# LAW: a parameter with no lowercase name of its own, a type parameter, is
# not counted
law arity_skips_type_parameter:
  for pp: Tree.Node
  for ps: List<&2, Tree.Node>
  for +acc: U32
  for e: {String.is_empty(Calls.param_name(pp)) == True{} : Bool}
  {Size.arity.go(pp <> ps, acc) == Size.arity.go(ps, acc) : U32}

# LAW: a parameter with a name of its own counts one
law arity_counts_named_parameter:
  for pp: Tree.Node
  for ps: List<&2, Tree.Node>
  for +acc: U32
  for e: {String.is_empty(Calls.param_name(pp)) == False{} : Bool}
  {Size.arity.go(pp <> ps, acc) == Size.arity.go(ps, (acc + 1 : U32)) : U32}

# LAW: a token on a later line than any before it is the last line so far
law last_takes_later_line:
  for k: Lex.TokKind
  for t: String
  for +l: U32
  for c: U32
  for +best: U32
  for e: {U32.is_gt(l, best) == True{} : Bool}
  {Size.last(Tree.Leaf{Lex.Tok{k, t, l, c}}, best) == l : U32}

# LAW: a token on no later line leaves the last line as it was
law last_keeps_earlier_line:
  for k: Lex.TokKind
  for t: String
  for +l: U32
  for c: U32
  for +best: U32
  for e: {U32.is_gt(l, best) == False{} : Bool}
  {Size.last(Tree.Leaf{Lex.Tok{k, t, l, c}}, best) == best : U32}

# LAW: the statements under one that opens a block sit one level down
law depth_block_goes_down:
  for kind: Tree.StmtKind
  for kids: Tree.Node
  for body: Tree.Node
  for rest: Tree.Node
  for +at: U32
  for best: U32
  for e: {Calls.has_colon(kids) == True{} : Bool}
  {Size.depth(Tree.NCons{Tree.Stmt{kind, kids, body}, rest}, at, best)
    == Size.depth(rest, at, Size.depth(body, (at + 1 : U32), Size.most(at, best))) : U32}

# LAW: the lines a statement that opens no block wrapped onto sit at its
# level
law depth_wrapped_line_stays:
  for kind: Tree.StmtKind
  for kids: Tree.Node
  for body: Tree.Node
  for rest: Tree.Node
  for +at: U32
  for best: U32
  for e: {Calls.has_colon(kids) == False{} : Bool}
  {Size.depth(Tree.NCons{Tree.Stmt{kind, kids, body}, rest}, at, best)
    == Size.depth(rest, at, Size.depth(body, at, Size.most(at, best))) : U32}
