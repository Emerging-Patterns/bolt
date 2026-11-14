# rules arity, length and depth: a def that holds more than a reader can.
# Each measures one thing of a def and reports the def when the measure is
# over the rule's limit, one finding on the def's name:
#   arity   its parameters, type parameters aside (`-A: Type`, `~A: Data`
#           have no lowercase name of their own): over 8
#   length  its lines, from the `def` line to the line of its last token:
#           over 40. A table is not measured: a def whose body is one
#           `match` with nothing under it but `case` arms, each holding at
#           most one statement, which opens no block
#   depth   how deep its statements nest. The statements right under the def
#           are level 1, and a statement that opens a block (its own tokens
#           hold a `:`, as `match x:` and `case A:` do) puts the statements
#           under it one level down: over 6, which is a third `match` inside
#           two
# A bolt.bend sets another limit with `def arity_max() -> U32`,
# `def length_max()` or `def depth_max()`.
# A line an expression wraps onto is under its statement in bolt's tree but
# opens no block, so it is no level. A block inside brackets (a lambda's
# body) is not read.
# Left alone: a law file, a proof file, and a def that is a proof (no type,
# or one that returns `-> {..}`), as the cost rules leave them
# (src/rules/calls.bend): a proof is as long as its statement needs.
# The fixes are structural, and a name cannot buy them: parameters that
# travel together become one value of a type; a step of a long def, or the
# inner match of a deep one, becomes a helper. A table has no step to move:
# its length is how many cases there are, and the one way to shorten it is
# to cut it in two at some line, which helps no reader. Of the 116 defs
# `length` reported in 82 public repos, 22 were tables.
# The limits are where public Bend 2 code stops: 99 in 100 defs have 9
# parameters or fewer, 19 lines or fewer, and nest 6 levels or fewer.
import Base
import ../../src.bend as Src
import ../../finding.bend as F
import ../../lazy/lazy.bend as Lazy
import ../../syntax/lex.bend as Lex
import ../../syntax/tree.bend as Tree
import ../calls.bend as Calls

# what of a def a rule measures
type Dim is Data:
  DArity{}
  DLength{}
  DDepth{}

# the rule's slug
def slug(dim: Dim) -> String:
  match dim:
    case DArity{}:
      "arity"
    case DLength{}:
      "length"
    case DDepth{}:
      "depth"

# the name a bolt.bend sets the rule's limit by
def limit_name(dim: Dim) -> String:
  match dim:
    case DArity{}:
      "arity_max"
    case DLength{}:
      "length_max"
    case DDepth{}:
      "depth_max"

# the rule's limit when no bolt.bend sets one
def limit(dim: Dim) -> U32:
  match dim:
    case DArity{}:
      8
    case DLength{}:
      40
    case DDepth{}:
      6

# the greater of two
def most(+a: U32, +b: U32) -> U32:
  Bool.pick(U32, U32.is_gt(a, b), a, b)

# one more when the parameter has a name of its own
def arity.one(name: String, +acc: U32) -> U32:
  Bool.pick(U32, String.is_empty(name), acc, (acc + 1 : U32))

# how many of the parameters have a name of their own, onto acc
def arity.go(ps: List<&2, Tree.Node>, acc: U32) -> U32:
  match ps:
    case Nil{}:
      acc
    case Con{p, rest}:
      arity.go(rest, arity.one(Calls.param_name(p), acc))

# a def's parameters, type parameters aside
def arity(sig: Tree.Node) -> U32:
  arity.go(Calls.params(sig), 0)

# a closing bracket's line, or the line so far
def last.close(close: Maybe<&2, Lex.Tok>, best: U32) -> U32:
  match close:
    case None{}:
      best
    case Some{Lex.Tok{_k, _t, l, _c}}:
      most(l, best)

# the greatest line of a token under the node, or best when it is greater
def last(n: Tree.Node, best: U32) -> U32:
  match n:
    case Tree.Leaf{Lex.Tok{_k, _t, l, _c}}:
      most(l, best)
    case Tree.Group{Lex.Tok{_k, _t, l, _c}, kids, close}:
      last.close(close, last(kids, most(l, best)))
    case Tree.Stmt{_kind, kids, body}:
      last(body, last(kids, best))
    case Tree.NNil{}:
      best
    case Tree.NCons{head, tail}:
      last(tail, last(head, best))

# a def's lines: from its first line to the line of its last token
def length(+sig: Tree.Node, body: Tree.Node) -> U32:
  +first = Tree.line(sig)
  (last(body, last(sig, first)) - first + 1 : U32)

# is this what an arm of a table holds: nothing under the `case` line, or
# one statement that opens no block?
def table.arm(body: Tree.Node) -> Bool:
  match body:
    case Tree.NNil{}:
      True{}
    case Tree.NCons{Tree.Stmt{_kind, kids, _under}, Tree.NNil{}}:
      Bool.not(Calls.has_colon(kids))
    case _other:
      False{}

# are these the arms of a table: `case` statements and nothing else, each
# holding what an arm of a table holds?
def table.arms(ns: Tree.Node) -> Bool:
  match ns:
    case Tree.NNil{}:
      True{}
    case Tree.NCons{Tree.Stmt{Tree.SCase{}, _kids, body}, rest}:
      Lazy.and_then(table.arm(body), _u => table.arms(rest))
    case _other:
      False{}

# is a def's body a table: one statement that opens a block, with the arms
# of a table under it?
def table(body: Tree.Node) -> Bool:
  match body:
    case Tree.NCons{Tree.Stmt{_kind, kids, arms}, Tree.NNil{}}:
      Lazy.and_then(Calls.has_colon(kids), _u => table.arms(arms))
    case _other:
      False{}

# the lines `length` holds a def to: none for a table
def length.of(+sig: Tree.Node, +body: Tree.Node) -> U32:
  Lazy.either(U32, table(body), _u => 0, _v => length(sig, body))

# the level the statements under a statement sit at: one down when it opens
# a block
def depth.under(opens: Bool, at: U32) -> U32:
  match opens:
    case True{}:
      (at + 1 : U32)
    case False{}:
      at

# the deepest level of a statement among these, which sit at level `at`, or
# best when it is deeper
def depth(n: Tree.Node, +at: U32, best: U32) -> U32:
  match n:
    case Tree.NCons{Tree.Stmt{_kind, kids, body}, rest}:
      depth(rest, at, depth(body, depth.under(Calls.has_colon(kids), at), most(at, best)))
    case Tree.NCons{_h, rest}:
      depth(rest, at, best)
    case _other:
      best

# what a rule measures of a def
def measure(dim: Dim, sig: Tree.Node, body: Tree.Node) -> U32:
  match dim:
    case DArity{}:
      arity(sig)
    case DLength{}:
      length.of(sig, body)
    case DDepth{}:
      depth(body, 1, 0)

# what a finding says
def say(dim: Dim, +name: String, size: U32, max: U32) -> String:
  match dim:
    case DArity{}:
      "Def " ++ name ++ " takes " ++ U32.show(size) ++ " parameters, more than " ++ U32.show(max)
        ++ "; make the ones that travel together one value of a type, or split the def."
    case DLength{}:
      "Def " ++ name ++ " is " ++ U32.show(size) ++ " lines long, more than " ++ U32.show(max)
        ++ "; move a step of it into a helper."
    case DDepth{}:
      "Def " ++ name ++ " nests " ++ U32.show(size) ++ " levels deep, more than " ++ U32.show(max)
        ++ "; move the inner match into a helper."

# a finding on the def's name when it is over, before the rest
def found(
  hit: Bool,
  +dim: Dim,
  +name: String,
  line: U32,
  size: U32,
  max: U32,
  path: String,
  more: List<&2, F.Finding>
) -> List<&2, F.Finding>:
  match hit:
    case True{}:
      F.Finding{path, line, 4, U32.from_nat(String.length(name)), slug(dim), say(dim, name, size, max)} <> more
    case False{}:
      more

# a def measured against the limit
def sized(
  +dim: Dim,
  name: String,
  line: U32,
  +size: U32,
  +max: U32,
  path: String,
  more: List<&2, F.Finding>
) -> List<&2, F.Finding>:
  found(U32.is_gt(size, max), dim, name, line, size, max, path, more)

# every def over the limit, in order; an exempt def is not measured
def check.go(ds: List<&2, Calls.Def>, +dim: Dim, +path: String, +max: U32) -> List<&2, F.Finding>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{Calls.Def{name, +sig, body}, rest}:
      +more = check.go(rest, dim, path, max)
      Lazy.stop(List<&2, F.Finding>, Calls.exempt(path, sig), more,
        _u => sized(dim, name, Tree.line(sig), measure(dim, sig, body), max, path, more))

# a rule of the family, at a limit
def check(dim: Dim, s: Src.Src, max: U32) -> List<&2, F.Finding>:
  Src.Src{path, _text, _toks, tree, _bound, _items} = s
  check.go(Calls.defs(tree), dim, path, max)
