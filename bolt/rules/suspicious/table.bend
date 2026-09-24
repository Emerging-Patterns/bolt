# rule table: `List.get` or `List.set` at a computed index inside a def that
# calls itself, when the list is a fixed table: a literal, an array, or
# `List.replicate` / `Array.new` / `List.range` with a constant count, written
# inline, defined beside the loop, or held by the let of that name in scope.
# The index walks that table on every step. Keep it in an Array. A let reaches
# the statements after it and the blocks under them, not a sibling case arm,
# and a later let of the name to anything else ends it. A literal index (a
# fixed slot, including 0 and 1), a growing or data-dependent list, a one-shot
# outside the recursion, and `List.head` / `List.tail` do not run. `index`
# leaves a table this rule owns, so one call is one finding. Laws and proofs
# do not run.
import Base
import ../../src.bend as Src
import ../../finding.bend as F
import ../../../syntax/lex.bend as Lex
import ../../../syntax/tree.bend as Tree
import ../calls.bend as Calls
import ../../../lazy/lazy.bend as Lazy

# is the chain exactly one number?
def literal(nn: Tree.Node) -> Bool:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TNum{}, t, l, c}}, Tree.NNil{}}:
      True{}
    case other:
      False{}

# a top-level token of this text, not one nested in a group
def top_has(nn: Tree.Node, +want: String) -> Bool:
  match nn:
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
def array_sized(nn: Tree.Node) -> Bool:
  match nn:
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
def lone_num(nn: Tree.Node) -> Bool:
  match nn:
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
def built_call(+tt: String, kids: Tree.Node) -> Bool:
  +as = Calls.args(kids)
  +rep = Bool.or(String.eq(tt, "List.replicate"), String.eq(tt, "Array.new"))
  Bool.or(Bool.and(rep, lone_num(Calls.arg(as, 2n))), Bool.and(String.eq(tt, "List.range"), range_count(as)))

# a list literal, a sized array, or a constant-size constructor
def built(nn: Tree.Node) -> Bool:
  match nn:
    case Tree.NCons{Tree.Group{Lex.Tok{k, +o, l, c}, +kids, close}, Tree.NNil{}}:
      Bool.and(String.eq(o, "["), Bool.or(top_has(kids, ","), Bool.and(top_has(kids, ":"), array_sized(kids))))
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, +t, l, c}},
        Tree.NCons{Tree.Group{Lex.Tok{_, +o, _, _}, +kids, _}, Tree.NNil{}}}:
      Bool.and(String.eq(o, "("), built_call(t, kids))
    case other:
      False{}

# the chain is exactly this call's name, with no arguments that matter: `name()`
def call_name(nn: Tree.Node) -> String:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, +t, l, c}},
        Tree.NCons{Tree.Group{Lex.Tok{_, +o, _, _}, kids, _}, Tree.NNil{}}}:
      Bool.pick(String, String.eq(o, "("), t, "")
    case other:
      ""

# the chain is exactly one lowercase name
def lone_name(nn: Tree.Node) -> String:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, +t, l, c}}, Tree.NNil{}}:
      t
    case other:
      ""

# one use of a name, told apart from its other uses by where it stands
def key(+tt: String, +line: U32, +col: U32) -> String:
  tt ++ "@" ++ U32.show(line) ++ ":" ++ U32.show(col)

# the chain is exactly one lowercase name: that use's key
def lone_key(nn: Tree.Node) -> String:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, +t, +l, +c}}, Tree.NNil{}}:
      key(t, l, c)
    case other:
      ""

# the list argument is a fixed table: inline, a use of a let that holds one,
# or `name()` / `name` for a table def of the file
def owns(+nn: Tree.Node, +fixed: List<&2, String>) -> Bool:
  +called = call_name(nn)
  +named = lone_name(nn)
  +used = lone_key(nn)
  Bool.or(built(nn), Bool.or(
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
def bind_name(nn: Tree.Node, +seen: Bool, +bad: Bool, +nm: String) -> String:
  match nn:
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
def bind_rhs(nn: Tree.Node) -> Tree.Node:
  match nn:
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
def use_at(+tt: String, +line: U32, +col: U32, +live: List<&2, String>, +acc: List<&2, String>) -> List<&2, String>:
  Bool.pick(List<&2, String>, List.contains(~String, ~String.eq, live, tt), key(tt, line, col) <> acc, acc)

# the keys of every name use under the node whose binding in scope is a
# table: a let reaches the statements after it and their bodies, not an
# enclosing block or a sibling arm, and a later let of the name replaces it
def lets(nn: Tree.Node, +live: List<&2, String>, acc: List<&2, String>) -> List<&2, String>:
  match nn:
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
  +tt: String,
  kids: Tree.Node,
  +fixed: List<&2, String>,
  +path: String,
  +line: U32,
  +col: U32
) -> List<&2, F.Finding>:
  +get = String.eq(tt, "List.get")
  +set = String.eq(tt, "List.set")
  +op = Bool.and(open, Bool.or(get, set))
  +as = Calls.args(kids)
  +fire = Bool.and(op, Bool.and(Bool.not(literal(Calls.arg(as, 3n))), owns(Calls.arg(as, 2n), fixed)))
  Bool.pick(List<&2, F.Finding>, fire,
    [cite(get, path, line, col, U32.from_nat(String.length(tt)))], [])

# every fixed-table get or set
def walk(nn: Tree.Node, +path: String, +fixed: List<&2, String>) -> List<&2, F.Finding>:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, +t, +l, +c}}, Tree.NCons{Tree.Group{Lex.Tok{_, +o, _, _}, +kids, _}, rest}}:
      +own = hit(String.eq(o, "("), t, kids, fixed, path, l, c)
      List.concat(&2, F.Finding, [own, walk(kids, path, fixed), walk(rest, path, fixed)])
    case Tree.NCons{Tree.Group{open, +kids, close}, rest}:
      List.concat(&2, F.Finding, [walk(kids, path, fixed), walk(rest, path, fixed)])
    case Tree.NCons{Tree.Stmt{kind, +kids, body}, rest}:
      List.concat(&2, F.Finding, [walk(kids, path, fixed), walk(body, path, fixed), walk(rest, path, fixed)])
    case Tree.NCons{h, rest}:
      walk(rest, path, fixed)
    case other:
      Nil{}

def check.go(
  ds: List<&2, Calls.Def>,
  +mods: List<&2, String>,
  +path: String,
  acc: List<&2, List<&2, F.Finding>>
) -> List<&2, F.Finding>:
  match ds:
    case Nil{}:
      List.concat(&2, F.Finding, List.reverse(&2, List<&2, F.Finding>, acc))
    case Con{Calls.Def{+name, +sig, +body}, rest}:
      check.go(rest, mods, path,
        Lazy.stop(List<&2, F.Finding>,
          Bool.not(Bool.and(Calls.calls(body, name), Bool.not(Calls.exempt(path, sig)))), [],
          _u => walk(body, path, scope(body, mods))) <> acc)

# the rule
def check(ss: Src.Src) -> List<&2, F.Finding>:
  Src.Src{path, text, toks, tree, bound, items} = ss
  +ds = Calls.defs(tree)
  check.go(ds, modules(ds, []), path, [])
