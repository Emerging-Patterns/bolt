# syntax/bind: where every name in a source is bound, and what every other
# name refers to. One walk over the tree threads an environment (the binders
# in scope, innermost first) through Bend's binding forms:
#   - an item's name (`def f`, `type T`, `law l`, a constructor line);
#   - a telescope: a def's parameters, a type's parameters, a constructor's
#     fields, each type seeing the names before it;
#   - `case p:` patterns and `for x: T` / `exs x: T where P`, for the lines
#     under them;
#   - a let (`x = v`, `+x = v`, `x : T = v`, `x : T <- m`, `a b = f g`,
#     `(a, K{b}) = p`) for the lines after it in its block -- the right side
#     sees the outer names, so `st = step(st)` reads the old st;
#   - `x => e`, `@x: A -> B` and `&x: A -> B`, for the rest of their sequence.
# The walk branches on token and statement kinds, never on a computed test,
# so each step recurses on one subtree and the checker accepts it.
# A binder shadows an item of the same name; a dotted name is an item of the
# file (`text.of`) or, through an import alias, of another file (`Lex.Tok`);
# anything else is free (Base, or unknown).
import Base
import ./lex.bend as Lex
import ../lazy/lazy.bend as Lazy
import ./tree.bend as Tree

# what a binder is: an item's or a constructor's name, a parameter, a type's
# parameter, a constructor's field, a let name, a pattern binder, a law's
# `for`, or a type-level `@x:` / `&x:`
type BindKind is Data:
  KItem{}
  KCtor{}
  KParam{}
  KTypeParam{}
  KField{}
  KLocal{}
  KPat{}
  KFor{}
  KTypeVar{}

# KLocal is a name a let, a do-bind or a lambda binds; KPat one bound by a
# pattern (a case, or a destructuring let). note: what to show for it -- a
# declaration's own text (`+x: U32`), else the line that bound it
type Bind is Data:
  Bind{name: String, line: U32, col: U32, kind: BindKind, note: String}

# what a use refers to: a binder of the file (by position), an item of the
# file, an item behind an import alias, or nothing known (Base, or unknown)
type Target is Data:
  TLocal{line: U32, col: U32}
  TItem{name: String}
  TQual{alias: String, name: String}
  TFree{}

# a name that is not a binder, with what it refers to
type Use is Data:
  Use{name: String, line: U32, col: U32, target: Target}

# the names in scope at a statement's line
type Scope is Data:
  Scope{line: U32, env: List<&2, Bind>}

# everything the binder knows about a source, each list in source order
type Bound is Data:
  Bound{binds: List<&2, Bind>, uses: List<&2, Use>, scopes: List<&2, Scope>}

# a line and a column
type Pos is Data:
  Pos{line: U32, col: U32}

# names of the file
# -----------------

# the item a statement declares: the first name after its keyword
def declared.go(kids: Tree.Node) -> Maybe<&2, String>:
  match kids:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, t, l, c}}, rest}:
      Some{t}
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TUpper{}, t, l, c}}, rest}:
      Some{t}
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TDotted{}, t, l, c}}, rest}:
      Some{t}
    case other:
      None{}

# the item a statement declares: the first name after its keyword
def declared(kids: Tree.Node) -> Maybe<&2, String>:
  match kids:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TKey{}, t, l, c}}, rest}:
      declared.go(rest)
    case Tree.NCons{h, rest}:
      declared(rest)
    case other:
      None{}

# a name, when there is one, onto a list
def push_name(mm: Maybe<&2, String>, acc: List<&2, String>) -> List<&2, String>:
  match mm:
    case None{}:
      acc
    case Some{name}:
      name <> acc

# a type's constructors: the first name of each line under it
def ctors(body: Tree.Node, acc: List<&2, String>) -> List<&2, String>:
  match body:
    case Tree.NCons{Tree.Stmt{k, kids, b}, rest}:
      ctors(rest, push_name(declared.go(kids), acc))
    case other:
      acc

# the defs, laws, types and constructors of a source
def items(root: Tree.Node, acc: List<&2, String>) -> List<&2, String>:
  match root:
    case Tree.NCons{Tree.Stmt{Tree.SDef{}, kids, body}, rest}:
      items(rest, push_name(declared(kids), acc))
    case Tree.NCons{Tree.Stmt{Tree.SLaw{}, kids, body}, rest}:
      items(rest, push_name(declared(kids), acc))
    case Tree.NCons{Tree.Stmt{Tree.SType{}, kids, body}, rest}:
      items(rest, ctors(body, push_name(declared(kids), acc)))
    case Tree.NCons{other, rest}:
      items(rest, acc)
    case other:
      acc

# the text of a chain's last leaf
def last_text(kids: Tree.Node) -> String:
  match kids:
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}}, Tree.NNil{}}:
      t
    case Tree.NCons{h, rest}:
      last_text(rest)
    case other:
      ""

# the import aliases of a source: the last token of each `import .. as X`
def aliases(root: Tree.Node, +acc: List<&2, String>) -> List<&2, String>:
  match root:
    case Tree.NCons{Tree.Stmt{Tree.SImport{}, kids, body}, rest}:
      +last = last_text(kids)
      aliases(rest, Bool.pick(List<&2, String>, Bool.or(String.eq(last, "Base"), String.eq(last, "import")), acc, last <> acc))
    case Tree.NCons{other, rest}:
      aliases(rest, acc)
    case other:
      acc

# resolution
# ----------

# the innermost binder of a name in an environment
def find(env: List<&2, Bind>, +name: String) -> Maybe<&2, Bind>:
  match env:
    case Nil{}:
      None{}
    case Con{Bind{+n, l, c, k, note}, t}:
      +more = find(t, name)
      Bool.pick(Maybe<&2, Bind>, String.eq(n, name), Some{Bind{n, l, c, k, note}}, more)

def head_of.go(cs: List<&2, Char>) -> List<&2, Char>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{+c, t}:
      Lazy.stop(List<&2, Char>, Char.is_eq(c, '.'), Nil{}, _u => c <> head_of.go(t))

# a dotted name's part before the first dot
def head_of(cs: List<&2, Char>) -> String:
  String.from_list(head_of.go(cs))

# a dotted name's part after the first dot
def rest_of(cs: List<&2, Char>) -> String:
  match cs:
    case Nil{}:
      ""
    case Con{c, +t}:
      Lazy.stop(String, Char.is_eq(c, '.'), String.from_list(t), _u => rest_of(t))

# is the name among these?
def has(names: List<&2, String>, +name: String) -> Bool:
  List.contains(~String, ~String.eq, names, name)

# the names an environment holds, and the file's items and aliases
type Names is Data:
  Names{items: List<&2, String>, aliases: List<&2, String>}

def resolve.local(mm: Maybe<&2, Bind>, +name: String, ns: Names) -> Target:
  match mm:
    case Some{Bind{n, l, c, k, note}}:
      TLocal{l, c}
    case None{}:
      Names{its, als} = ns
      +cs = String.to_list(name)
      +head = head_of(cs)
      Bool.pick(Target, has(its, name), TItem{name},
        Lazy.stop(Target, Bool.not(Bool.and(String.contains(name, "."), has(als, head))), TFree{},
          _u => TQual{head, rest_of(cs)}))

# what a name at a point refers to, given what is in scope
def resolve(env: List<&2, Bind>, +name: String, ns: Names) -> Target:
  resolve.local(find(env, name), name, ns)

# the walk
# --------

# what the walk has gathered so far, each list reversed
type Out is Data:
  Out{binds: List<&2, Bind>, uses: List<&2, Use>, scopes: List<&2, Scope>}

# what the walk is reading; MLhs and MLhsType carry the environment the
# right side of the let will see, and MLhs the kind its names bind with
type Mode is Data:
  MBlock{}
  MCtors{}
  MCtor{}
  MHead{}
  MName{}
  MSig{}
  MTele{kind: BindKind}
  MTeleType{kind: BindKind}
  MLhs{outer: List<&2, Bind>, kind: BindKind}
  MLhsType{outer: List<&2, Bind>}
  MTerm{}

# the walk's result: the environment after, and the output
type W is Data:
  W{env: List<&2, Bind>, out: Out}

# a new binder, into the environment and the output
def bind(+name: String, +line: U32, +col: U32, kind: BindKind, env: List<&2, Bind>, out: Out) -> W:
  Out{binds, uses, scopes} = out
  +b = {Bind{name, line, col, kind, ""} : Bind}
  W{b <> env, Out{b <> binds, uses, scopes}}

# a declaration as written: `+x: List<&2, U32>`, `~f: U32 -> U32`. A space
# follows `:` and `,`, spaces surround `->`, everything else is glued
def spaced(+tt: String) -> String:
  Bool.pick(String, String.eq(tt, "->"), " -> ",
    Bool.pick(String, Bool.or(String.eq(tt, ":"), String.eq(tt, ",")), tt ++ " ", tt))

# a group's close bracket, "" when it never closed
def render_close(close: Maybe<&2, Lex.Tok>) -> String:
  match close:
    case None{}:
      ""
    case Some{Lex.Tok{k, t, l, c}}:
      t

# the text of a whole chain
def render_all(nn: Tree.Node) -> String:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}}, rest}:
      spaced(t) ++ render_all(rest)
    case Tree.NCons{Tree.Group{Lex.Tok{k, t, l, c}, kids, close}, rest}:
      t ++ render_all(kids) ++ render_close(close) ++ render_all(rest)
    case other:
      ""

# the text of a chain up to its first comma
def render(nn: Tree.Node) -> String:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TComma{}, t, l, c}}, rest}:
      ""
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, t, l, c}}, rest}:
      spaced(t) ++ render(rest)
    case Tree.NCons{Tree.Group{Lex.Tok{k, t, l, c}, kids, close}, rest}:
      t ++ render_all(kids) ++ render_close(close) ++ render(rest)
    case other:
      ""

# a telescope binder, with its declaration as the note: the quantity before
# it, its name, and the rest up to the comma
def bind_decl(
  +name: String,
  +line: U32,
  +col: U32,
  kind: BindKind,
  +quantity: String,
  rest: Tree.Node,
  env: List<&2, Bind>,
  out: Out
) -> W:
  Out{binds, uses, scopes} = out
  +b = {Bind{name, line, col, kind, quantity ++ name ++ render(rest)} : Bind}
  W{b <> env, Out{b <> binds, uses, scopes}}

# a use of a name, resolved against the environment
def use(+name: String, line: U32, col: U32, +env: List<&2, Bind>, ns: Names, out: Out) -> W:
  Out{binds, uses, scopes} = out
  W{env, Out{binds, Use{name, line, col, resolve(env, name, ns)} <> uses, scopes}}

# the names in scope at a statement's line, recorded
def mark(line: U32, +env: List<&2, Bind>, out: Out) -> Out:
  Out{binds, uses, scopes} = out
  Out{binds, uses, Scope{line, env} <> scopes}

# what the names of a telescope bind as, by its bracket: `(` parameters,
# `<` type parameters, `{` fields
def tele_kind(+oo: String) -> BindKind:
  Bool.pick(BindKind, String.eq(oo, "("), KParam{},
    Bool.pick(BindKind, String.eq(oo, "<"), KTypeParam{}, KField{}))

# a result's environment
def env_of(ww: W) -> List<&2, Bind>:
  W{env, out} = ww
  env

# a result's output
def out_of(ww: W) -> Out:
  W{env, out} = ww
  out

# the walk: one node in one mode, against an environment. Every recursive
# call is on a subtree (kids, body, gkids or rest), never on n itself
def walk(nn: Tree.Node, mode: Mode, +env: List<&2, Bind>, +ns: Names, out: Out) -> W:
  match nn mode:
    # statements
    case Tree.NCons{Tree.Stmt{Tree.SDef{}, +kids, body}, rest} MBlock{}:
      +h = walk(kids, MHead{}, env, ns, out)
      +b = walk(body, MBlock{}, env_of(h), ns, mark(Tree.line(kids), env_of(h), out_of(h)))
      walk(rest, MBlock{}, env, ns, out_of(b))
    case Tree.NCons{Tree.Stmt{Tree.SLaw{}, kids, body}, rest} MBlock{}:
      +h = walk(kids, MHead{}, env, ns, out)
      +b = walk(body, MBlock{}, env_of(h), ns, out_of(h))
      walk(rest, MBlock{}, env, ns, out_of(b))
    case Tree.NCons{Tree.Stmt{Tree.SType{}, kids, body}, rest} MBlock{}:
      +h = walk(kids, MHead{}, env, ns, out)
      +b = walk(body, MCtors{}, env_of(h), ns, out_of(h))
      walk(rest, MBlock{}, env, ns, out_of(b))
    case Tree.NCons{Tree.Stmt{Tree.SImport{}, kids, body}, rest} MBlock{}:
      walk(rest, MBlock{}, env, ns, out)
    case Tree.NCons{Tree.Stmt{Tree.SCase{}, +kids, body}, rest} MBlock{}:
      +p = walk(kids, MLhs{env, KPat{}}, env, ns, mark(Tree.line(kids), env, out))
      +b = walk(body, MBlock{}, env_of(p), ns, out_of(p))
      walk(rest, MBlock{}, env, ns, out_of(b))
    case Tree.NCons{Tree.Stmt{Tree.SFor{}, +kids, body}, rest} MBlock{}:
      +f = walk(kids, MLhs{env, KFor{}}, env, ns, mark(Tree.line(kids), env, out))
      +b = walk(body, MBlock{}, env_of(f), ns, out_of(f))
      walk(rest, MBlock{}, env_of(f), ns, out_of(b))
    case Tree.NCons{Tree.Stmt{Tree.SLet{}, +kids, body}, rest} MBlock{}:
      +l = walk(kids, MLhs{env, KLocal{}}, env, ns, mark(Tree.line(kids), env, out))
      +b = walk(body, MBlock{}, env_of(l), ns, out_of(l))
      walk(rest, MBlock{}, env_of(l), ns, out_of(b))
    case Tree.NCons{Tree.Stmt{Tree.STerm{}, +kids, body}, rest} MBlock{}:
      +t = walk(kids, MTerm{}, env, ns, mark(Tree.line(kids), env, out))
      +b = walk(body, MBlock{}, env_of(t), ns, out_of(t))
      walk(rest, MBlock{}, env, ns, out_of(b))
    # a type's constructor lines
    case Tree.NCons{Tree.Stmt{k, +kids, body}, rest} MCtors{}:
      +c = walk(kids, MCtor{}, env, ns, mark(Tree.line(kids), env, out))
      walk(rest, MCtors{}, env, ns, out_of(c))
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TUpper{}, t, l, c}}, rest} MCtor{}:
      +w = bind(t, l, c, KCtor{}, env, out)
      walk(rest, MSig{}, env, ns, out_of(w))
    case Tree.NCons{h, rest} MCtor{}:
      walk(rest, MSig{}, env, ns, out)
    # an item's header: skip to its keyword, then its name, then its signature
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TKey{}, t, l, c}}, rest} MHead{}:
      walk(rest, MName{}, env, ns, out)
    case Tree.NCons{h, rest} MHead{}:
      walk(rest, MHead{}, env, ns, out)
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, t, l, c}}, rest} MName{}:
      +w = bind(t, l, c, KItem{}, env, out)
      walk(rest, MSig{}, env, ns, out_of(w))
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TUpper{}, t, l, c}}, rest} MName{}:
      +w = bind(t, l, c, KItem{}, env, out)
      walk(rest, MSig{}, env, ns, out_of(w))
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TDotted{}, t, l, c}}, rest} MName{}:
      +w = bind(t, l, c, KItem{}, env, out)
      walk(rest, MSig{}, env, ns, out_of(w))
    case Tree.NCons{h, rest} MName{}:
      walk(rest, MSig{}, env, ns, out)
    case Tree.NCons{Tree.Group{Lex.Tok{k, t, l, c}, gkids, close}, rest} MSig{}:
      +p = walk(gkids, MTele{tele_kind(t)}, env, ns, out)
      walk(rest, MTerm{}, env_of(p), ns, out_of(p))
    case Tree.NCons{h, rest} MSig{}:
      walk(rest, MTerm{}, env, ns, out)
    # a telescope: names bind, `:` starts a type that runs to the next comma
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TOp{}, q, ql, qc}},
      Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, t, l, c}}, rest}} MTele{+kind}:
      +r = {rest : Tree.Node}
      +w = bind_decl(t, l, c, kind, q, r, env, out)
      walk(r, MTele{kind}, env_of(w), ns, out_of(w))
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TOp{}, q, ql, qc}},
      Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TUpper{}, t, l, c}}, rest}} MTele{+kind}:
      +r = {rest : Tree.Node}
      +w = bind_decl(t, l, c, kind, q, r, env, out)
      walk(r, MTele{kind}, env_of(w), ns, out_of(w))
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, t, l, c}}, rest} MTele{+kind}:
      +r = {rest : Tree.Node}
      +w = bind_decl(t, l, c, kind, "", r, env, out)
      walk(r, MTele{kind}, env_of(w), ns, out_of(w))
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TUpper{}, t, l, c}}, rest} MTele{+kind}:
      +r = {rest : Tree.Node}
      +w = bind_decl(t, l, c, kind, "", r, env, out)
      walk(r, MTele{kind}, env_of(w), ns, out_of(w))
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TColon{}, t, l, c}}, rest} MTele{+kind}:
      walk(rest, MTeleType{kind}, env, ns, out)
    case Tree.NCons{h, rest} MTele{+kind}:
      walk(rest, MTele{kind}, env, ns, out)
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TComma{}, t, l, c}}, rest} MTeleType{+kind}:
      walk(rest, MTele{kind}, env, ns, out)
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TAll{}, t, l, c}}, Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, x, xl, xc}},
      Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TColon{}, ct, cl, cc}}, rest}}} MTeleType{+kind}:
      +w = bind(x, xl, xc, KTypeVar{}, env, out)
      walk(rest, MTeleType{kind}, env_of(w), ns, out_of(w))
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, t, l, c}}, rest} MTeleType{+kind}:
      +w = use(t, l, c, env, ns, out)
      walk(rest, MTeleType{kind}, env, ns, out_of(w))
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TUpper{}, t, l, c}}, rest} MTeleType{+kind}:
      +w = use(t, l, c, env, ns, out)
      walk(rest, MTeleType{kind}, env, ns, out_of(w))
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TDotted{}, t, l, c}}, rest} MTeleType{+kind}:
      +w = use(t, l, c, env, ns, out)
      walk(rest, MTeleType{kind}, env, ns, out_of(w))
    case Tree.NCons{Tree.Group{open, gkids, close}, rest} MTeleType{+kind}:
      +g = walk(gkids, MTerm{}, env, ns, out)
      walk(rest, MTeleType{kind}, env, ns, out_of(g))
    case Tree.NCons{h, rest} MTeleType{+kind}:
      walk(rest, MTeleType{kind}, env, ns, out)
    # a pattern, or a let's left side: names bind, `K{..}` and `(..)` nest
    # (as patterns), `:` starts a type, `=` / `<-` start the right side
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TUpper{}, t, l, c}},
      Tree.NCons{Tree.Group{open, gkids, close}, rest}} MLhs{+outer, kind}:
      +w = use(t, l, c, env, ns, out)
      +g = walk(gkids, MLhs{outer, KPat{}}, env, ns, out_of(w))
      walk(rest, MLhs{outer, KPat{}}, env_of(g), ns, out_of(g))
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TDotted{}, t, l, c}},
      Tree.NCons{Tree.Group{open, gkids, close}, rest}} MLhs{+outer, kind}:
      +w = use(t, l, c, env, ns, out)
      +g = walk(gkids, MLhs{outer, KPat{}}, env, ns, out_of(w))
      walk(rest, MLhs{outer, KPat{}}, env_of(g), ns, out_of(g))
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, t, l, c}}, rest} MLhs{+outer, +kind}:
      +w = bind(t, l, c, kind, env, out)
      walk(rest, MLhs{outer, kind}, env_of(w), ns, out_of(w))
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TUpper{}, t, l, c}}, rest} MLhs{+outer, +kind}:
      +w = bind(t, l, c, kind, env, out)
      walk(rest, MLhs{outer, kind}, env_of(w), ns, out_of(w))
    case Tree.NCons{Tree.Group{open, gkids, close}, rest} MLhs{+outer, kind}:
      +g = walk(gkids, MLhs{outer, KPat{}}, env, ns, out)
      walk(rest, MLhs{outer, KPat{}}, env_of(g), ns, out_of(g))
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TColon{}, t, l, c}}, rest} MLhs{outer, kind}:
      walk(rest, MLhsType{outer}, env, ns, out)
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TEq{}, t, l, c}}, rest} MLhs{outer, kind}:
      +r = walk(rest, MTerm{}, outer, ns, out)
      W{env, out_of(r)}
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TBind{}, t, l, c}}, rest} MLhs{outer, kind}:
      +r = walk(rest, MTerm{}, outer, ns, out)
      W{env, out_of(r)}
    case Tree.NCons{h, rest} MLhs{outer, kind}:
      walk(rest, MLhs{outer, kind}, env, ns, out)
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TEq{}, t, l, c}}, rest} MLhsType{+outer}:
      +r = walk(rest, MTerm{}, outer, ns, out)
      W{env, out_of(r)}
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TBind{}, t, l, c}}, rest} MLhsType{+outer}:
      +r = walk(rest, MTerm{}, outer, ns, out)
      W{env, out_of(r)}
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, t, l, c}}, rest} MLhsType{+outer}:
      +w = use(t, l, c, env, ns, out)
      walk(rest, MLhsType{outer}, env, ns, out_of(w))
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TUpper{}, t, l, c}}, rest} MLhsType{+outer}:
      +w = use(t, l, c, env, ns, out)
      walk(rest, MLhsType{outer}, env, ns, out_of(w))
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TDotted{}, t, l, c}}, rest} MLhsType{+outer}:
      +w = use(t, l, c, env, ns, out)
      walk(rest, MLhsType{outer}, env, ns, out_of(w))
    case Tree.NCons{Tree.Group{open, gkids, close}, rest} MLhsType{+outer}:
      +g = walk(gkids, MTerm{}, env, ns, out)
      walk(rest, MLhsType{outer}, env, ns, out_of(g))
    case Tree.NCons{h, rest} MLhsType{+outer}:
      walk(rest, MLhsType{outer}, env, ns, out)
    # terms: names are uses; `x =>`, `@x:` and `&x:` bind for the rest
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, t, l, c}},
      Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TLam{}, lt, ll, lc}}, rest}} MTerm{}:
      +w = bind(t, l, c, KLocal{}, env, out)
      walk(rest, MTerm{}, env_of(w), ns, out_of(w))
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TAll{}, t, l, c}}, Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, x, xl, xc}},
      Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TColon{}, ct, cl, cc}}, rest}}} MTerm{}:
      +w = bind(x, xl, xc, KTypeVar{}, env, out)
      walk(rest, MTerm{}, env_of(w), ns, out_of(w))
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TAll{}, t, l, c}}, Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TUpper{}, x, xl, xc}},
      Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TColon{}, ct, cl, cc}}, rest}}} MTerm{}:
      +w = bind(x, xl, xc, KTypeVar{}, env, out)
      walk(rest, MTerm{}, env_of(w), ns, out_of(w))
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TAmp{}, t, l, c}}, Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, x, xl, xc}},
      Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TColon{}, ct, cl, cc}}, rest}}} MTerm{}:
      +w = bind(x, xl, xc, KTypeVar{}, env, out)
      walk(rest, MTerm{}, env_of(w), ns, out_of(w))
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, t, l, c}}, rest} MTerm{}:
      +w = use(t, l, c, env, ns, out)
      walk(rest, MTerm{}, env, ns, out_of(w))
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TUpper{}, t, l, c}}, rest} MTerm{}:
      +w = use(t, l, c, env, ns, out)
      walk(rest, MTerm{}, env, ns, out_of(w))
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TDotted{}, t, l, c}}, rest} MTerm{}:
      +w = use(t, l, c, env, ns, out)
      walk(rest, MTerm{}, env, ns, out_of(w))
    case Tree.NCons{Tree.Group{open, gkids, close}, rest} MTerm{}:
      +g = walk(gkids, MTerm{}, env, ns, out)
      walk(rest, MTerm{}, env, ns, out_of(g))
    case Tree.NCons{h, rest} MTerm{}:
      walk(rest, MTerm{}, env, ns, out)
    case other m:
      W{env, out}

# notes
# -----

# leading spaces dropped
def lstrip(cs: List<&2, Char>) -> List<&2, Char>:
  match cs:
    case Con{' ', t}:
      lstrip(t)
    case other:
      other

# the n-th line of a source, without its indentation
def line_text(lines: List<&2, String>, nn: U32) -> String:
  String.from_list(lstrip(String.to_list(Maybe.default(&2, String, List.get(&2, String, lines, U32.to_nat(nn)), ""))))

# a declaration carries its own note; anything else shows the line that
# bound it
def note_for(kind: BindKind, +note: String, lines: List<&2, String>, line: U32) -> String:
  match kind:
    case KParam{}:
      note
    case KField{}:
      note
    case KTypeParam{}:
      note
    case other:
      line_text(lines, line)

# every binder with its note filled
def annotate(binds: List<&2, Bind>, +lines: List<&2, String>) -> List<&2, Bind>:
  match binds:
    case Nil{}:
      Nil{}
    case Con{Bind{name, +line, col, +kind, note}, rest}:
      Bind{name, line, col, kind, note_for(kind, note, lines, line)} <> annotate(rest, lines)

# putting it together
# -------------------

# the gathered output, in source order and annotated
def finish(oo: Out, lines: List<&2, String>) -> Bound:
  Out{binds, uses, scopes} = oo
  Bound{annotate(List.reverse(&2, Bind, binds), lines), List.reverse(&2, Use, uses), List.reverse(&2, Scope, scopes)}

# the binding structure of a parsed source
def of_tree(+root: Tree.Node, lines: List<&2, String>) -> Bound:
  finish(out_of(walk(root, MBlock{}, [], Names{items(root, []), aliases(root, [])}, Out{[], [], []})), lines)

# the binding structure of a source
def bound(+source: String) -> Bound:
  of_tree(Tree.parse(source), String.lines(source))

# queries
# -------

# where a name is: a binder, or a use of one
type Site is Data:
  SBind{bind: Bind}
  SUse{use: Use}

# does the name at (l, c) cover the position (line, col)?
def covers(+l2: U32, +c2: U32, +name: String, +line: U32, +col: U32) -> Bool:
  +end = (c2 + U32.from_nat(String.length(name)) : U32)
  Bool.and(U32.is_eq(l2, line), Bool.and(U32.is_le(c2, col), U32.is_lt(col, end)))

# the binder whose name covers a position
def bind_at(binds: List<&2, Bind>, +line: U32, +col: U32) -> Maybe<&2, Site>:
  match binds:
    case Nil{}:
      None{}
    case Con{Bind{+name, +l, +c, kind, note}, rest}:
      +more = bind_at(rest, line, col)
      Bool.pick(Maybe<&2, Site>, covers(l, c, name, line, col), Some{SBind{Bind{name, l, c, kind, note}}}, more)

# the use whose name covers a position
def use_at(uses: List<&2, Use>, +line: U32, +col: U32) -> Maybe<&2, Site>:
  match uses:
    case Nil{}:
      None{}
    case Con{Use{+name, +l, +c, tg}, rest}:
      +more = use_at(rest, line, col)
      Bool.pick(Maybe<&2, Site>, covers(l, c, name, line, col), Some{SUse{Use{name, l, c, tg}}}, more)

def at.or(mm: Maybe<&2, Site>, uses: List<&2, Use>, line: U32, col: U32) -> Maybe<&2, Site>:
  match mm:
    case Some{site}:
      Some{site}
    case None{}:
      use_at(uses, line, col)

# the site at a position
def at(bb: Bound, +line: U32, +col: U32) -> Maybe<&2, Site>:
  Bound{binds, uses, scopes} = bb
  at.or(bind_at(binds, line, col), uses, line, col)

# the binder at a position (a use's target, or the binder itself)
def binder(binds: List<&2, Bind>, +line: U32, +col: U32) -> Maybe<&2, Bind>:
  match binds:
    case Nil{}:
      None{}
    case Con{Bind{name, +l, +c, kind, note}, rest}:
      +more = binder(rest, line, col)
      +here = Bool.and(U32.is_eq(l, line), U32.is_eq(c, col))
      Bool.pick(Maybe<&2, Bind>, here, Some{Bind{name, l, c, kind, note}}, more)

# the names in scope at a line: those of the statement on it, else of the
# nearest statement above
def visible.go(scopes: List<&2, Scope>, +qline: U32, best: List<&2, Bind>) -> List<&2, Bind>:
  match scopes:
    case Nil{}:
      best
    case Con{Scope{+line, env}, rest}:
      +hit = U32.is_le(line, qline)
      visible.go(rest, qline, Bool.pick(List<&2, Bind>, hit, env, best))

# the scopes hold binders before their notes were filled: read each back
def noted(mm: Maybe<&2, Bind>, bb: Bind) -> Bind:
  match mm:
    case None{}:
      bb
    case Some{full}:
      full

# each binder of an environment, with the note its annotated twin carries
def refresh(env: List<&2, Bind>, +binds: List<&2, Bind>) -> List<&2, Bind>:
  match env:
    case Nil{}:
      Nil{}
    case Con{Bind{name, +l, +c, kind, note}, rest}:
      noted(binder(binds, l, c), Bind{name, l, c, kind, note}) <> refresh(rest, binds)

# the names in scope at a line: those of the statement on it, else of the
# nearest statement above
def visible(bb: Bound, qline: U32) -> List<&2, Bind>:
  Bound{binds, uses, scopes} = bb
  refresh(visible.go(scopes, qline, []), binds)

# every position a binder is named at: its own, then its uses'
def sites.go(uses: List<&2, Use>, +line: U32, +col: U32) -> List<&2, Pos>:
  match uses:
    case Nil{}:
      Nil{}
    case Con{Use{name, l, c, TLocal{+tl, +tc}}, rest}:
      +more = sites.go(rest, line, col)
      Bool.pick(List<&2, Pos>, Bool.and(U32.is_eq(tl, line), U32.is_eq(tc, col)), Pos{l, c} <> more, more)
    case Con{other, rest}:
      sites.go(rest, line, col)

# every position a binder is named at: its own, then its uses'
def sites(bb: Bound, +line: U32, +col: U32) -> List<&2, Pos>:
  Bound{binds, uses, scopes} = bb
  Pos{line, col} <> sites.go(uses, line, col)

# every position an item of the file is named at: its declaration, then its
# uses
def item_sites.binds(binds: List<&2, Bind>, +name: String) -> List<&2, Pos>:
  match binds:
    case Nil{}:
      Nil{}
    case Con{Bind{+n, l, c, KItem{}, note}, rest}:
      +more = item_sites.binds(rest, name)
      Bool.pick(List<&2, Pos>, String.eq(n, name), Pos{l, c} <> more, more)
    case Con{Bind{+n, l, c, KCtor{}, note}, rest}:
      +more = item_sites.binds(rest, name)
      Bool.pick(List<&2, Pos>, String.eq(n, name), Pos{l, c} <> more, more)
    case Con{other, rest}:
      item_sites.binds(rest, name)

def item_sites.uses(uses: List<&2, Use>, +name: String) -> List<&2, Pos>:
  match uses:
    case Nil{}:
      Nil{}
    case Con{Use{n, l, c, TItem{+t}}, rest}:
      +more = item_sites.uses(rest, name)
      Bool.pick(List<&2, Pos>, String.eq(t, name), Pos{l, c} <> more, more)
    case Con{other, rest}:
      item_sites.uses(rest, name)

# every position an item of the file is named at: its declaration, then its
# uses
def item_sites(bb: Bound, +name: String) -> List<&2, Pos>:
  Bound{binds, uses, scopes} = bb
  List.append(&2, Pos, item_sites.binds(binds, name), item_sites.uses(uses, name))

# every position a name not of this file is used at (Base, or through an
# alias)
def named_sites.go(uses: List<&2, Use>, +name: String) -> List<&2, Pos>:
  match uses:
    case Nil{}:
      Nil{}
    case Con{Use{+n, l, c, TLocal{tl, tc}}, rest}:
      named_sites.go(rest, name)
    case Con{Use{+n, l, c, tg}, rest}:
      +more = named_sites.go(rest, name)
      Bool.pick(List<&2, Pos>, String.eq(n, name), Pos{l, c} <> more, more)

# every position a name not of this file is used at (Base, or through an
# alias)
def named_sites(bb: Bound, +name: String) -> List<&2, Pos>:
  Bound{binds, uses, scopes} = bb
  named_sites.go(uses, name)

# the kind of the binder at a position, for what a use looks like
def kind_at(binds: List<&2, Bind>, +line: U32, +col: U32) -> Maybe<&2, BindKind>:
  match binds:
    case Nil{}:
      None{}
    case Con{Bind{name, +l, +c, kind, note}, rest}:
      +more = kind_at(rest, line, col)
      Bool.pick(Maybe<&2, BindKind>, Bool.and(U32.is_eq(l, line), U32.is_eq(c, col)), Some{kind}, more)

# the kind of an item or constructor of the file, by name
def kind_of_item(binds: List<&2, Bind>, +name: String) -> Maybe<&2, BindKind>:
  match binds:
    case Nil{}:
      None{}
    case Con{Bind{+n, l, c, KItem{}, note}, rest}:
      +more = kind_of_item(rest, name)
      Bool.pick(Maybe<&2, BindKind>, String.eq(n, name), Some{KItem{}}, more)
    case Con{Bind{+n, l, c, KCtor{}, note}, rest}:
      +more = kind_of_item(rest, name)
      Bool.pick(Maybe<&2, BindKind>, String.eq(n, name), Some{KCtor{}}, more)
    case Con{other, rest}:
      kind_of_item(rest, name)
