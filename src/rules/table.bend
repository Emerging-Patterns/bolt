# src/rules/table: what a fixed table is, for `index`. A fixed table is a
# literal list, an array, or `List.replicate` / `Array.new` / `List.range`
# with a constant count, written inline, defined beside the loop, or held by
# the let of that name in scope; a let reaches the statements after it and
# the blocks under them, not a sibling case arm, and a later let of the name
# to anything else ends it. `index` leaves a get of one alone. This was the
# `table` rule (U008), retired: it had no public hits; `hit` still builds the
# finding that rule gave, which `index` reads only as "a fixed table". Pure.
import Base
import ../finding.bend as F
import ../syntax/lex.bend as Lex
import ../syntax/tree.bend as Tree
import ./calls.bend as Calls

# is the chain exactly one number?
def literal(n: Tree.Node) -> Bool:
  match n:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TNum{}, t, l, c}}, Tree.NNil{}}:
      True{}
    case other:
      False{}

# a top-level token of this text, not one nested in a group
def top_has(n: Tree.Node, +want: String) -> Bool:
  match n:
    case Tree.NCons{Tree.Group{open, kids, close}, rest}:
      top_has(rest, want)
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, +t, l, c}}, rest}:
      +more = top_has(rest, want)
      Bool.or(String.eq(t, want), more)
    case Tree.NCons{h, rest}:
      top_has(rest, want)
    case other:
      False{}

# `[v : T*n]` or `[v : T^d]`, and the size is a number
def array_sized(n: Tree.Node) -> Bool:
  match n:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TOp{}, +op, l, c}},
        Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TNum{}, t, l2, c2}}, rest}}:
      +here = Bool.or(String.eq(op, "*"), String.eq(op, "^"))
      +more = array_sized(rest)
      Bool.or(here, more)
    case Tree.NCons{Tree.Group{open, kids, close}, rest}:
      array_sized(rest)
    case Tree.NCons{h, rest}:
      array_sized(rest)
    case other:
      False{}

# the chain is exactly one number
def lone_num(n: Tree.Node) -> Bool:
  match n:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TNum{}, t, l, c}}, Tree.NNil{}}:
      True{}
    case other:
      False{}

# `List.replicate` / `Array.new` count at argument 2; `List.range` at the end
def range_count(as: List<&2, Tree.Node>) -> Bool:
  match as:
    case Nil{}:
      False{}
    case Con{h, Nil{}}:
      lone_num(h)
    case Con{h, rest}:
      range_count(rest)

# a constant-size constructor, not a length taken from the data
def built_call(+t: String, kids: Tree.Node) -> Bool:
  +as = Calls.args(kids)
  +rep = Bool.or(String.eq(t, "List.replicate"), String.eq(t, "Array.new"))
  Bool.or(Bool.and(rep, lone_num(Calls.arg(as, 2n))), Bool.and(String.eq(t, "List.range"), range_count(as)))

# a list literal, a sized array, or a constant-size constructor
def built(n: Tree.Node) -> Bool:
  match n:
    case Tree.NCons{Tree.Group{Lex.Tok{k, +o, l, c}, +kids, close}, Tree.NNil{}}:
      Bool.and(String.eq(o, "["), Bool.or(top_has(kids, ","), Bool.and(top_has(kids, ":"), array_sized(kids))))
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, +t, l, c}},
        Tree.NCons{Tree.Group{Lex.Tok{_, +o, _, _}, +kids, _}, Tree.NNil{}}}:
      Bool.and(String.eq(o, "("), built_call(t, kids))
    case other:
      False{}

# the chain is exactly this call's name, with no arguments that matter: `name()`
def call_name(n: Tree.Node) -> String:
  match n:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, +t, l, c}},
        Tree.NCons{Tree.Group{Lex.Tok{_, +o, _, _}, kids, _}, Tree.NNil{}}}:
      Bool.pick(String, String.eq(o, "("), t, "")
    case other:
      ""

# the chain is exactly one lowercase name
def lone_name(n: Tree.Node) -> String:
  match n:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, +t, l, c}}, Tree.NNil{}}:
      t
    case other:
      ""

# one use of a name, told apart from its other uses by where it stands
def key(+t: String, +line: U32, +col: U32) -> String:
  t ++ "@" ++ U32.show(line) ++ ":" ++ U32.show(col)

# the chain is exactly one lowercase name: that use's key
def lone_key(n: Tree.Node) -> String:
  match n:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, +t, +l, +c}}, Tree.NNil{}}:
      key(t, l, c)
    case other:
      ""

# the list argument is a fixed table: inline, a use of a let that holds one,
# or `name()` / `name` for a table def of the file
def owns(+n: Tree.Node, +fixed: List<&2, String>) -> Bool:
  +called = call_name(n)
  +named = lone_name(n)
  +used = lone_key(n)
  Bool.or(built(n), Bool.or(
    Bool.and(Bool.not(String.is_empty(named)),
      Bool.or(List.contains(~String, ~String.eq, fixed, named), List.contains(~String, ~String.eq, fixed, used))),
    Bool.and(Bool.not(String.is_empty(called)), List.contains(~String, ~String.eq, fixed, called))))

# one plain name before `=`, when the pattern is not a destructure
def bind_bad(+bad: Bool, +nm: String) -> String:
  match bad:
    case True{}:
      ""
    case False{}:
      nm

# one plain name before `=`, when there is one
def bind_at(+seen: Bool, +bad: Bool, +nm: String) -> String:
  match seen:
    case False{}:
      ""
    case True{}:
      bind_bad(bad, nm)

# the one plain name a statement binds, or empty
def bind_name(n: Tree.Node, +seen: Bool, +bad: Bool, +nm: String) -> String:
  match n:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TEq{}, t, l, c}}, rest}:
      bind_at(seen, bad, nm)
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, +t, l, c}}, rest}:
      bind_name(rest, True{}, Bool.or(bad, seen), t)
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TUpper{}, t, l, c}}, rest}:
      bind_name(rest, seen, True{}, nm)
    case Tree.NCons{Tree.Group{open, kids, close}, rest}:
      bind_name(rest, seen, bad, nm)
    case Tree.NCons{h, rest}:
      bind_name(rest, seen, bad, nm)
    case other:
      ""

# the right-hand side: the chain after a statement's top-level `=`
def bind_rhs(n: Tree.Node) -> Tree.Node:
  match n:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TEq{}, t, l, c}}, rest}:
      rest
    case Tree.NCons{h, rest}:
      bind_rhs(rest)
    case other:
      Tree.NNil{}

# the names in scope without this one
def drop(live: List<&2, String>, +nm: String) -> List<&2, String>:
  match live:
    case Nil{}:
      []
    case Con{+h, rest}:
      +more = drop(rest, nm)
      Bool.pick(List<&2, String>, String.eq(h, nm), more, h <> more)

# after a let of `nm`: it holds a table only when this binding is one
def rebind(+nm: String, +tab: Bool, +live: List<&2, String>) -> List<&2, String>:
  +out = drop(live, nm)
  Bool.pick(List<&2, String>, String.is_empty(nm), live,
    Bool.pick(List<&2, String>, tab, nm <> out, out))

# a name use joins the keys when the let in scope for it holds a table
def use_at(+t: String, +line: U32, +col: U32, +live: List<&2, String>, +acc: List<&2, String>) -> List<&2, String>:
  Bool.pick(List<&2, String>, List.contains(~String, ~String.eq, live, t), key(t, line, col) <> acc, acc)

# the keys of every name use under the node whose binding in scope is a
# table: a let reaches the statements after it and their bodies, not an
# enclosing block or a sibling arm, and a later let of the name replaces it
def lets(n: Tree.Node, +live: List<&2, String>, acc: List<&2, String>) -> List<&2, String>:
  match n:
    case Tree.NCons{Tree.Stmt{kind, +kids, body}, rest}:
      +next = rebind(bind_name(kids, False{}, False{}, ""), built(bind_rhs(kids)), live)
      lets(rest, next, lets(body, live, lets(kids, live, acc)))
    case Tree.NCons{Tree.Group{open, +kids, close}, rest}:
      lets(rest, live, lets(kids, live, acc))
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, +t, +l, +c}}, rest}:
      lets(rest, live, use_at(t, l, c, live, acc))
    case Tree.NCons{h, rest}:
      lets(rest, live, acc)
    case other:
      acc

# a def whose body is one fixed table
def mod_one(body: Tree.Node, +name: String, +acc: List<&2, String>) -> List<&2, String>:
  match body:
    case Tree.NCons{Tree.Stmt{kind, +kids, inn}, Tree.NNil{}}:
      Bool.pick(List<&2, String>, built(kids), name <> acc, acc)
    case other:
      acc

# defs of this file whose body is one fixed table
def modules(ds: List<&2, Calls.Def>, acc: List<&2, String>) -> List<&2, String>:
  match ds:
    case Nil{}:
      acc
    case Con{Calls.Def{+name, sig, +body}, rest}:
      modules(rest, mod_one(body, name, acc))

# fixed tables visible in this def: the file's table defs by name, and each
# use of a let whose binding in scope is a table, by its key
def scope(body: Tree.Node, +mods: List<&2, String>) -> List<&2, String>:
  lets(body, [], mods)

# the finding for a get or a set
def cite(+get: Bool, +path: String, +line: U32, +col: U32, +len: U32) -> F.Finding:
  match get:
    case True{}:
      F.Finding{path, line, col, len, "table",
        "List.get in a recursive def walks the table from its head on every step; keep the table in an Array and use Array.get."}
    case False{}:
      F.Finding{path, line, col, len, "table",
        "List.set in a recursive def copies the list to change one element; keep the table in an Array and use Array.set."}

# a get or a set of a fixed table at a computed index
def hit(
  +open: Bool,
  +t: String,
  kids: Tree.Node,
  +fixed: List<&2, String>,
  +path: String,
  +line: U32,
  +col: U32
) -> List<&2, F.Finding>:
  +get = String.eq(t, "List.get")
  +set = String.eq(t, "List.set")
  +op = Bool.and(open, Bool.or(get, set))
  +as = Calls.args(kids)
  +fire = Bool.and(op, Bool.and(Bool.not(literal(Calls.arg(as, 3n))), owns(Calls.arg(as, 2n), fixed)))
  Bool.pick(List<&2, F.Finding>, fire,
    [cite(get, path, line, col, U32.from_nat(String.length(t)))], [])
