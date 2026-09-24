# rule hoist: a fixed table built inside a def that calls itself, from inputs
# that do not change, and then indexed. The build runs again on every step.
# Build it once, outside the recursion. A build is a list or array literal,
# `List.replicate` / `List.range` / `List.map` / `Array.new` / `Array.map`, or
# a call to a def of this file whose body is itself one fixed table of more
# than eight cells; a def whose body cannot be seen (another module's) is not
# a build. A table of eight cells or fewer is left alone, and so is a build
# whose arguments depend on the step. A name that is not a carried parameter
# (a pattern binder, a value computed on the step) keeps the build; a case arm
# that does not recurse is cold; laws and proofs do not run (a def with no
# type at all fills a law: it is a proof). `List.get` itself stays with
# `index`.
import Base
import ../../src.bend as Src
import ../../finding.bend as F
import ../../../syntax/lex.bend as Lex
import ../../../syntax/tree.bend as Tree
import ../calls.bend as Calls
import ../../../lazy/lazy.bend as Lazy
import ./table.bend as Table

# where an accessor reads its collection, when it is one
type Slot is Data:
  Slot{on: Bool, at: Nat}

# a `name = expr` whose left side is one plain name
type Got is Data:
  Got{nm: String, expr: Tree.Node}

# which argument a get or set indexes
def slot_pick(+list: Bool, +str: Bool, +arr: Bool) -> Slot:
  match list str arr:
    case True{} b c:
      Slot{True{}, 2n}
    case False{} True{} c:
      Slot{True{}, 0n}
    case False{} False{} True{}:
      Slot{True{}, 1n}
    case False{} False{} False{}:
      Slot{False{}, 0n}

# List.get / List.set read argument 2, String.get argument 0, Array.get / Array.set argument 1
def slot_of(+tt: String) -> Slot:
  slot_pick(
    Bool.or(String.eq(tt, "List.get"), String.eq(tt, "List.set")),
    String.eq(tt, "String.get"),
    Bool.or(String.eq(tt, "Array.get"), String.eq(tt, "Array.set")))

# the self-calls' argument lists
def pushes(nn: Tree.Node, +self: String) -> List<&2, List<&2, Tree.Node>>:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, +t, l, c}}, Tree.NCons{Tree.Group{Lex.Tok{_, +o, _, _}, +kids, _}, rest}}:
      +me = Bool.and(String.eq(o, "("), String.eq(t, self))
      +more = List.concat(&2, List<&2, Tree.Node>, [pushes(kids, self), pushes(rest, self)])
      Bool.pick(List<&2, List<&2, Tree.Node>>, me, Calls.args(kids) <> more, more)
    case Tree.NCons{Tree.Group{open, +kids, close}, rest}:
      List.concat(&2, List<&2, Tree.Node>, [pushes(kids, self), pushes(rest, self)])
    case Tree.NCons{Tree.Stmt{kind, +kids, body}, rest}:
      List.concat(&2, List<&2, Tree.Node>, [pushes(kids, self), pushes(body, self), pushes(rest, self)])
    case Tree.NCons{h, rest}:
      pushes(rest, self)
    case other:
      Nil{}

# is the chain exactly this name?
def lone_eq(nn: Tree.Node, +name: String) -> Bool:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, +t, l, c}}, Tree.NNil{}}:
      String.eq(t, name)
    case other:
      False{}

# every self-call passes this same name at this argument
def all_same(cs: List<&2, List<&2, Tree.Node>>, +ii: Nat, +name: String) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{as, rest}:
      +here = lone_eq(Calls.arg(as, ii), name)
      +more = all_same(rest, ii, name)
      Bool.and(here, more)

# parameters every self-call passes unchanged, when there is a self-call
def carried.go(
  ps: List<&2, Tree.Node>,
  +cs: List<&2, List<&2, Tree.Node>>,
  +ii: Nat,
  +acc: List<&2, String>
) -> List<&2, String>:
  match ps:
    case Nil{}:
      List.reverse(&2, String, acc)
    case Con{p, rest}:
      +nm = Calls.param_name(p)
      +keep = Bool.and(Bool.not(String.is_empty(nm)), all_same(cs, ii, nm))
      carried.go(rest, cs, (ii + 1n : Nat), Bool.pick(List<&2, String>, keep, nm <> acc, acc))

# parameters passed through unchanged; empty when nothing recurses
def carried_of(cs: List<&2, List<&2, Tree.Node>>, +sig: Tree.Node) -> List<&2, String>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      carried.go(Calls.params(sig), h <> t, 0n, [])

# parameters passed through unchanged; empty when nothing recurses
def carried(sig: Tree.Node, body: Tree.Node, +self: String) -> List<&2, String>:
  carried_of(pushes(body, self), sig)

# a plain name is closed only when it is a carried parameter; a type or a dotted name is
def name_ok(kk: Lex.TokKind, +tt: String, +carried: List<&2, String>) -> Bool:
  match kk:
    case Lex.TName{}:
      List.contains(~String, ~String.eq, carried, tt)
    case other:
      True{}

# a token after an operator: a template argument is not a value, anything else is
def leaf_ok(+skip: Bool, tok: Lex.Tok, +carried: List<&2, String>) -> Bool:
  match skip:
    case True{}:
      True{}
    case False{}:
      Lex.Tok{+k, +t, l, c} = tok
      name_ok(k, t, carried)

# an application is closed in its arguments; a bracketed name is a value
def value_ok(+app: Bool, kk: Lex.TokKind, +tt: String, +carried: List<&2, String>) -> Bool:
  match app:
    case True{}:
      True{}
    case False{}:
      name_ok(kk, tt, carried)

# every value name under the node is a carried parameter (callees and templates are not values)
def closed(nn: Tree.Node, +carried: List<&2, String>) -> Bool:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TOp{}, +op, l, c}}, Tree.NCons{Tree.Leaf{+tok}, tail}}:
      +ok = leaf_ok(String.eq(op, "~"), tok, carried)
      +aft = closed(tail, carried)
      Bool.and(ok, aft)
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TOp{}, op, l, c}}, rest}:
      closed(rest, carried)
    case Tree.NCons{Tree.Leaf{Lex.Tok{+k, +t, l, c}}, Tree.NCons{Tree.Group{Lex.Tok{_, +o, _, _}, +kids, _}, rest}}:
      +ok = value_ok(String.eq(o, "("), k, t, carried)
      +inn = closed(kids, carried)
      +aft = closed(rest, carried)
      Bool.and(ok, Bool.and(inn, aft))
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, +t, l, c}}, rest}:
      +ok = List.contains(~String, ~String.eq, carried, t)
      +aft = closed(rest, carried)
      Bool.and(ok, aft)
    case Tree.NCons{Tree.Leaf{tok}, rest}:
      closed(rest, carried)
    case Tree.NCons{Tree.Group{open, +kids, close}, rest}:
      +inn = closed(kids, carried)
      +aft = closed(rest, carried)
      Bool.and(inn, aft)
    case Tree.NCons{Tree.Stmt{kind, +kids, body}, rest}:
      +inn = closed(kids, carried)
      +bod = closed(body, carried)
      +aft = closed(rest, carried)
      Bool.and(inn, Bool.and(bod, aft))
    case Tree.NCons{h, rest}:
      closed(rest, carried)
    case Tree.Leaf{Lex.Tok{Lex.TName{}, +t, l, c}}:
      List.contains(~String, ~String.eq, carried, t)
    case other:
      True{}

# a top-level token of this text, not one nested in a group
def top_mark(nn: Tree.Node, +want: String) -> Bool:
  match nn:
    case Tree.NCons{Tree.Group{open, kids, close}, rest}:
      top_mark(rest, want)
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, +t, l, c}}, rest}:
      +more = top_mark(rest, want)
      Bool.or(String.eq(t, want), more)
    case Tree.NCons{h, rest}:
      top_mark(rest, want)
    case other:
      False{}

# `[v : T*n]` or `[v : T^d]`: an array, not a list
def is_array(+kids: Tree.Node) -> Bool:
  +col = top_mark(kids, ":")
  +star = top_mark(kids, "*")
  +hat = top_mark(kids, "^")
  Bool.and(col, Bool.or(star, hat))

# how many top-level copies of this token
def top_count(nn: Tree.Node, +want: String, +got: Nat) -> Nat:
  match nn:
    case Tree.NCons{Tree.Group{open, kids, close}, rest}:
      top_count(rest, want, got)
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, +t, l, c}}, rest}:
      +next = Bool.pick(Nat, String.eq(t, want), (got + 1n : Nat), got)
      top_count(rest, want, next)
    case Tree.NCons{h, rest}:
      top_count(rest, want, got)
    case other:
      got

# a number literal of eight or fewer
def small_num(+tt: String) -> Bool:
  List.contains(~String, ~String.eq,
    ["0", "1", "2", "3", "4", "5", "6", "7", "8", "0n", "1n", "2n", "3n", "4n", "5n", "6n", "7n", "8n"], tt)

# the size after `*` is a literal of eight or fewer, or the depth after `^` (2^d slots) three or fewer
def small_size(nn: Tree.Node) -> Bool:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TOp{}, +op, l, c}},
        Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TNum{}, +t, l2, c2}}, rest}}:
      +here = Bool.or(Bool.and(String.eq(op, "*"), small_num(t)),
        Bool.and(String.eq(op, "^"), List.contains(~String, ~String.eq, ["0", "1", "2", "3", "0n", "1n", "2n", "3n"], t)))
      +more = small_size(rest)
      Bool.or(here, more)
    case Tree.NCons{Tree.Group{open, kids, close}, rest}:
      small_size(rest)
    case Tree.NCons{h, rest}:
      small_size(rest)
    case other:
      False{}

# more than eight cells: nine or more list elements, or an array whose size is not that small
def wide_shape(+arr: Bool, +kids: Tree.Node) -> Bool:
  match arr:
    case True{}:
      Bool.not(small_size(kids))
    case False{}:
      Nat.is_gt(top_count(kids, ",", 0n), 7n)

# constructors that build a fixed table rather than walk one
def allowed(+tt: String) -> Bool:
  List.contains(~String, ~String.eq,
    ["List.replicate", "List.range", "List.map", "Array.new", "Array.map"], tt)

# a Base constructor on the allow list, or a def of this file whose body is
# itself a wide table (`wides`); a def whose body cannot be seen is not one
def builder(kk: Lex.TokKind, +tt: String, +self: String, +wides: List<&2, String>) -> Bool:
  match kk:
    case Lex.TName{}:
      Bool.and(Bool.not(String.eq(tt, self)), List.contains(~String, ~String.eq, wides, tt))
    case Lex.TDotted{}:
      Bool.or(allowed(tt), List.contains(~String, ~String.eq, wides, tt))
    case other:
      False{}

# a bracket group that is a closed list or array of more than eight cells
def group_yes(+arr: Bool, +kids: Tree.Node, +carried: List<&2, String>) -> Bool:
  +shape = Bool.or(top_mark(kids, ","), arr)
  +ok = closed(kids, carried)
  +wide = wide_shape(arr, kids)
  Bool.and(shape, Bool.and(ok, wide))

# a bracket group that is a closed list or array
def table_group(+brack: Bool, +kids: Tree.Node, +carried: List<&2, String>) -> Bool:
  match brack:
    case False{}:
      False{}
    case True{}:
      group_yes(is_array(kids), kids, carried)

# the chain is exactly one number; its text, or empty
def num_text(nn: Tree.Node) -> String:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TNum{}, +t, l, c}}, Tree.NNil{}}:
      t
    case other:
      ""

# a count is wide when it is not a literal of eight or fewer (a name may be large)
def count_wide(aa: Tree.Node) -> Bool:
  Bool.not(small_num(num_text(aa)))

# the last argument
def last_node(as: List<&2, Tree.Node>) -> Tree.Node:
  match as:
    case Nil{}:
      Tree.NNil{}
    case Con{h, Nil{}}:
      h
    case Con{h, rest}:
      last_node(rest)

# `List.replicate` / `Array.new` take argument 2; anything else is wide unless it is `List.range`
def call_arm(rep: Bool, +as: List<&2, Tree.Node>, +end: Tree.Node, +range: Bool) -> Bool:
  match rep:
    case True{}:
      count_wide(Calls.arg(as, 2n))
    case False{}:
      Bool.pick(Bool, range, count_wide(end), True{})

# `List.replicate` / `Array.new` / `List.range` are wide unless their count is a small literal
def call_wide(+tt: String, kids: Tree.Node) -> Bool:
  +as = Calls.args(kids)
  call_arm(Bool.or(String.eq(tt, "List.replicate"), String.eq(tt, "Array.new")), as, last_node(as), String.eq(tt, "List.range"))

# a call that builds a table from closed arguments, and is not a small literal count
def table_built(+ok: Bool, +wide: Bool, kids: Tree.Node, +carried: List<&2, String>) -> Bool:
  match ok wide:
    case True{} True{}:
      closed(kids, carried)
    case True{} False{}:
      False{}
    case False{} b:
      False{}

# a call that builds a table from closed arguments
def table_call(
  +app: Bool,
  kk: Lex.TokKind,
  +tt: String,
  +kids: Tree.Node,
  +self: String,
  +wides: List<&2, String>,
  +carried: List<&2, String>
) -> Bool:
  match app:
    case False{}:
      False{}
    case True{}:
      table_built(builder(kk, tt, self, wides), call_wide(tt, kids), kids, carried)

# a fixed table of more than eight cells, whatever its cells read
def wide_of(nn: Tree.Node) -> Bool:
  match nn:
    case Tree.NCons{Tree.Group{Lex.Tok{k, +o, l, c}, +kids, close}, Tree.NNil{}}:
      wide_shape(is_array(kids), kids)
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, +t, l, c}},
        Tree.NCons{Tree.Group{Lex.Tok{_, +o, _, _}, +kids, _}, Tree.NNil{}}}:
      call_wide(t, kids)
    case other:
      False{}

# a def whose body is one wide fixed table (`Table.built`, and more than eight cells)
def wide_one(body: Tree.Node, +name: String, +acc: List<&2, String>) -> List<&2, String>:
  match body:
    case Tree.NCons{Tree.Stmt{kind, +kids, inn}, Tree.NNil{}}:
      Bool.pick(List<&2, String>, Bool.and(Table.built(kids), wide_of(kids)), name <> acc, acc)
    case other:
      acc

# defs of this file whose body is one wide fixed table
def wide_defs(ds: List<&2, Calls.Def>, acc: List<&2, String>) -> List<&2, String>:
  match ds:
    case Nil{}:
      acc
    case Con{Calls.Def{+name, sig, +body}, rest}:
      wide_defs(rest, wide_one(body, name, acc))

# a list, an array, or a builder call, closed over carried parameters
def is_table(nn: Tree.Node, +self: String, +wides: List<&2, String>, +carried: List<&2, String>) -> Bool:
  match nn:
    case Tree.NCons{Tree.Group{Lex.Tok{k, +o, l, c}, +kids, close}, Tree.NNil{}}:
      table_group(String.eq(o, "["), kids, carried)
    case Tree.NCons{Tree.Leaf{Lex.Tok{+k, +t, l, c}},
        Tree.NCons{Tree.Group{Lex.Tok{_, +o, _, _}, +kids, _}, Tree.NNil{}}}:
      table_call(String.eq(o, "("), k, t, kids, self, wides, carried)
    case other:
      False{}

# drop the right-hand side
def skip_expr(nn: Tree.Node) -> Maybe<&2, Got>:
  match nn:
    case other:
      None{}

# the chain after `=`, when the left side is one plain name and nothing else
def got_bad(+bad: Bool, +nm: String, expr: Tree.Node) -> Maybe<&2, Got>:
  match bad:
    case True{}:
      skip_expr(expr)
    case False{}:
      Some{Got{nm, expr}}

# the chain after `=`, when exactly one plain name stands before it
def got_at(+seen: Bool, +bad: Bool, +nm: String, expr: Tree.Node) -> Maybe<&2, Got>:
  match seen:
    case False{}:
      skip_expr(expr)
    case True{}:
      got_bad(bad, nm, expr)

# a second name, a constructor or a group on the left is not a plain binder
def eat(nn: Tree.Node, +seen: Bool, +bad: Bool, +nm: String) -> Maybe<&2, Got>:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TEq{}, t, l, c}}, rest}:
      got_at(seen, bad, nm, rest)
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, +t, l, c}}, rest}:
      eat(rest, True{}, Bool.or(bad, seen), t)
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TUpper{}, t, l, c}}, rest}:
      eat(rest, seen, True{}, nm)
    case Tree.NCons{Tree.Group{open, kids, close}, rest}:
      eat(rest, seen, True{}, nm)
    case Tree.NCons{h, rest}:
      eat(rest, seen, bad, nm)
    case other:
      None{}

# a finding on the table expression
def cite(+nn: Tree.Node, +path: String) -> List<&2, F.Finding>:
  [F.Finding{path, Tree.line(nn), Tree.col(nn), U32.from_nat(String.length(Tree.text(nn))), "hoist",
    "This table is rebuilt on every step from inputs that do not change; build it once, outside the recursion."}]

# a name, and nothing after it
def wrapped_inside(nn: Tree.Node, +binder: String) -> Bool:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, +t, l, c}}, Tree.NNil{}}:
      String.eq(t, binder)
    case other:
      False{}

# inside one pair of parentheses
def wrapped_open(+paren: Bool, kids: Tree.Node, +binder: String) -> Bool:
  match paren:
    case True{}:
      wrapped_inside(kids, binder)
    case False{}:
      False{}

# the chain is exactly this name, or that name in parentheses
def wrapped(nn: Tree.Node, +binder: String) -> Bool:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, +t, l, c}}, Tree.NNil{}}:
      String.eq(t, binder)
    case Tree.NCons{Tree.Group{Lex.Tok{k, +o, l, c}, +kids, close}, Tree.NNil{}}:
      wrapped_open(String.eq(o, "("), kids, binder)
    case other:
      False{}

# the collection argument is this name
def uses_arg(ss: Slot, +as: List<&2, Tree.Node>, +binder: String) -> Bool:
  Slot{on, at} = ss
  match on:
    case False{}:
      False{}
    case True{}:
      wrapped(Calls.arg(as, at), binder)

# `name[` is an index; a call is an index when its collection argument is the name
def uses_here_call(+call: Bool, +tt: String, kids: Tree.Node, +binder: String) -> Bool:
  match call:
    case False{}:
      False{}
    case True{}:
      uses_arg(slot_of(tt), Calls.args(kids), binder)

# `name[` is an index; a call is an index when its collection argument is the name
def uses_here(+brack: Bool, +call: Bool, +tt: String, kids: Tree.Node, +binder: String) -> Bool:
  match brack:
    case True{}:
      String.eq(tt, binder)
    case False{}:
      uses_here_call(call, tt, kids, binder)

# the name is indexed later: `name[`, or the collection of a get or set
def uses_name(nn: Tree.Node, +binder: String) -> Bool:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, +t, l, c}}, Tree.NCons{Tree.Group{Lex.Tok{_, +o, _, _}, +kids, _}, rest}}:
      +here = uses_here(String.eq(o, "["), String.eq(o, "("), t, kids, binder)
      +inn = uses_name(kids, binder)
      +aft = uses_name(rest, binder)
      Bool.or(here, Bool.or(inn, aft))
    case Tree.NCons{Tree.Group{open, +kids, close}, rest}:
      +inn = uses_name(kids, binder)
      +aft = uses_name(rest, binder)
      Bool.or(inn, aft)
    case Tree.NCons{Tree.Stmt{kind, +kids, body}, rest}:
      +inn = uses_name(kids, binder)
      +bod = uses_name(body, binder)
      +aft = uses_name(rest, binder)
      Bool.or(inn, Bool.or(bod, aft))
    case Tree.NCons{h, rest}:
      uses_name(rest, binder)
    case other:
      False{}

# indexed in the let's body or in a following statement
def uses_or(body: Tree.Node, rest: Tree.Node, +binder: String) -> Bool:
  +inn = uses_name(body, binder)
  +aft = uses_name(rest, binder)
  Bool.or(inn, aft)

# a finding when the table is also indexed
def let_used(+used: Bool, +expr: Tree.Node, +path: String) -> List<&2, F.Finding>:
  match used:
    case True{}:
      cite(expr, path)
    case False{}:
      Nil{}

# a finding when the right-hand side is a closed table that is indexed
def let_use(+tab: Bool, +used: Bool, +expr: Tree.Node, +path: String) -> List<&2, F.Finding>:
  match tab:
    case False{}:
      Nil{}
    case True{}:
      let_used(used, expr, path)

# a plain let of a table
def let_of(
  mm: Maybe<&2, Got>,
  +body: Tree.Node,
  +rest: Tree.Node,
  +self: String,
  +wides: List<&2, String>,
  +carried: List<&2, String>,
  +path: String
) -> List<&2, F.Finding>:
  match mm:
    case None{}:
      Nil{}
    case Some{Got{+nm, +expr}}:
      let_use(is_table(expr, self, wides, carried), uses_or(body, rest, nm), expr, path)

# a hot plain let of a table that is indexed afterwards
def let_hit(
  +hot: Bool,
  kids: Tree.Node,
  +body: Tree.Node,
  +rest: Tree.Node,
  +self: String,
  +wides: List<&2, String>,
  +carried: List<&2, String>,
  +path: String
) -> List<&2, F.Finding>:
  match hot:
    case False{}:
      Nil{}
    case True{}:
      let_of(eat(kids, False{}, False{}, ""), body, rest, self, wides, carried, path)

# a finding when this argument is itself a closed table
def one_yes(+yes: Bool, +aa: Tree.Node, +path: String) -> List<&2, F.Finding>:
  match yes:
    case True{}:
      cite(aa, path)
    case False{}:
      Nil{}

# the collection argument, when this call indexes one
def arg_table(
  ss: Slot,
  +as: List<&2, Tree.Node>,
  +self: String,
  +wides: List<&2, String>,
  +carried: List<&2, String>,
  +path: String
) -> List<&2, F.Finding>:
  Slot{on, at} = ss
  match on:
    case False{}:
      Nil{}
    case True{}:
      +aa = Calls.arg(as, at)
      one_yes(is_table(aa, self, wides, carried), aa, path)

# an inline table passed straight to a get or set, when the group is a call
def call_open(
  +open: Bool,
  +tt: String,
  kids: Tree.Node,
  +self: String,
  +wides: List<&2, String>,
  +carried: List<&2, String>,
  +path: String
) -> List<&2, F.Finding>:
  match open:
    case False{}:
      Nil{}
    case True{}:
      arg_table(slot_of(tt), Calls.args(kids), self, wides, carried, path)

# an inline table passed straight to a get or set
def call_table(
  +hot: Bool,
  +open: Bool,
  +tt: String,
  kids: Tree.Node,
  +self: String,
  +wides: List<&2, String>,
  +carried: List<&2, String>,
  +path: String
) -> List<&2, F.Finding>:
  match hot:
    case False{}:
      Nil{}
    case True{}:
      call_open(open, tt, kids, self, wides, carried, path)

# a `=>` cools the rest of its chain: a lambda's body runs when it is called, not per step
def warm(+hot: Bool, kk: Lex.TokKind) -> Bool:
  match kk:
    case Lex.TLam{}:
      False{}
    case other:
      hot

# tables built in a hot region
def walk(
  nn: Tree.Node,
  +self: String,
  +wides: List<&2, String>,
  +carried: List<&2, String>,
  +path: String,
  +hot: Bool
) -> List<&2, F.Finding>:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, +t, l, c}}, Tree.NCons{Tree.Group{Lex.Tok{_, +o, _, _}, +kids, _}, rest}}:
      +heat = warm(hot, k)
      +own = call_table(heat, String.eq(o, "("), t, kids, self, wides, carried, path)
      +inn = walk(kids, self, wides, carried, path, heat)
      +aft = walk(rest, self, wides, carried, path, heat)
      List.concat(&2, F.Finding, [own, inn, aft])
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}}, rest}:
      walk(rest, self, wides, carried, path, warm(hot, k))
    case Tree.NCons{Tree.Group{open, +kids, close}, rest}:
      List.concat(&2, F.Finding,
        [walk(kids, self, wides, carried, path, hot), walk(rest, self, wides, carried, path, hot)])
    case Tree.NCons{Tree.Stmt{Tree.SCase{}, kids, +body}, rest}:
      +arm = Bool.and(hot, Calls.calls(body, self))
      List.concat(&2, F.Finding, [walk(kids, self, wides, carried, path, False{}),
        walk(body, self, wides, carried, path, arm), walk(rest, self, wides, carried, path, hot)])
    case Tree.NCons{Tree.Stmt{kind, +kids, +body}, +rest}:
      +own = let_hit(hot, kids, body, rest, self, wides, carried, path)
      List.concat(&2, F.Finding, [own, walk(kids, self, wides, carried, path, hot),
        walk(body, self, wides, carried, path, hot), walk(rest, self, wides, carried, path, hot)])
    case Tree.NCons{h, rest}:
      walk(rest, self, wides, carried, path, hot)
    case other:
      Nil{}

def check.go(
  ds: List<&2, Calls.Def>,
  +wide: List<&2, String>,
  +path: String,
  acc: List<&2, List<&2, F.Finding>>
) -> List<&2, F.Finding>:
  match ds:
    case Nil{}:
      List.concat(&2, F.Finding, List.reverse(&2, List<&2, F.Finding>, acc))
    case Con{Calls.Def{+name, +sig, +body}, rest}:
      check.go(rest, wide, path,
        Lazy.stop(List<&2, F.Finding>,
          Bool.not(Bool.and(Calls.calls(body, name), Bool.not(Calls.exempt(path, sig)))), [],
          _u => walk(body, name, wide, carried(sig, body, name), path, True{})) <> acc)

# the rule
def check(ss: Src.Src) -> List<&2, F.Finding>:
  Src.Src{path, text, toks, tree, bound, items} = ss
  +ds = Calls.defs(tree)
  check.go(ds, wide_defs(ds, []), path, [])
