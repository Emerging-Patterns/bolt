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

# a name that can be declared: plain, capitalized or dotted
def declared.is_name(kk: Lex.TokKind) -> Bool:
  match kk:
    case Lex.TName{}:
      True{}
    case Lex.TUpper{}:
      True{}
    case Lex.TDotted{}:
      True{}
    case other:
      False{}

# a leaf's name, when its kind is one: the kind is tested, the text only kept
def declared.name(nn: Tree.Node) -> Maybe<&2, String>:
  match nn:
    case Tree.Leaf{Lex.Tok{k, t, l, c}}:
      Bool.pick(Maybe<&2, String>, declared.is_name(k), Some{t}, None{})
    case other:
      None{}

# the item a statement declares: the first name after its keyword
def declared.go(kids: Tree.Node) -> Maybe<&2, String>:
  match kids:
    case Tree.NCons{h, rest}:
      declared.name(h)
    case other:
      None{}

# a keyword?
def declared.is_key(kk: Lex.TokKind) -> Bool:
  match kk:
    case Lex.TKey{}:
      True{}
    case other:
      False{}

# a keyword leaf? its kind is read, never its text
def declared.key(nn: Tree.Node) -> Bool:
  match nn:
    case Tree.Leaf{Lex.Tok{k, t, l, c}}:
      declared.is_key(k)
    case other:
      False{}

# the item a statement declares: the first name after its keyword
def declared(kids: Tree.Node) -> Maybe<&2, String>:
  match kids:
    case Tree.NCons{h, +rest}:
      Lazy.either(Maybe<&2, String>, declared.key(h), _u => declared.go(rest), _v => declared(rest))
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

# two names alike, char by char, stopping at the first that differs:
# String.eq, without the pairs String.cmp builds on every step
def same(aa: String, bb: String) -> Bool:
  match aa bb:
    case SNil{} SNil{}:
      True{}
    case SNil{} SCon{_h2, _t2}:
      False{}
    case SCon{_h1, _t1} SNil{}:
      False{}
    case SCon{h1, t1} SCon{h2, t2}:
      Lazy.and_then(Char.is_eq(h1, h2), _u => same(t1, t2))

# is the name among the file's items? `has`, stopping at the first hit, as
# every use no binder holds asks it of every item
def has_item(names: List<&2, String>, +name: String) -> Bool:
  match names:
    case Nil{}:
      False{}
    case Con{hh, rest}:
      Lazy.or_else(same(hh, name), _u => has_item(rest, name))

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
      Bool.pick(Target, has_item(its, name), TItem{name},
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
# right side of the let will see, and MLhs the kind its names bind with.
# MSkip steps over one node (a name a form already bound), then reads on in
# next; MStop reads nothing more
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
  MSkip{next: Mode}
  MStop{}

# the walk's result: the environment after, and the output
type W is Data:
  W{env: List<&2, Bind>, out: Out}

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

# the plan of a step
# ------------------
# The walk takes a node apart only as far as its head (a leaf, a group, a
# statement, or anything else), and recurses on the head's parts and on the
# rest of the chain. What each step does -- the mode it reads the rest in,
# whether it binds or uses a name, which environment it passes on -- is
# decided by the plain defs below, from the mode, the head and a peek at the
# rest. The forms that need a peek (`K{..}`, `op name`, `x =>`, `@x:`, `&x:`)
# read the rest from where they are, and a name the form already bound is
# stepped over in MSkip.

# does the chain start with a leaf of this kind?
def plan.lam(rest: Tree.Node) -> Bool:
  match rest:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TLam{}, _t, _l, _c}}, _r}:
      True{}
    case _other:
      False{}

# does the chain start with a group?
def plan.group(rest: Tree.Node) -> Bool:
  match rest:
    case Tree.NCons{Tree.Group{_o, _g, _cl}, _r}:
      True{}
    case _other:
      False{}

# does the chain start with a name (lower or upper case)?
def plan.named(rest: Tree.Node) -> Bool:
  match rest:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, _t, _l, _c}}, _r}:
      True{}
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TUpper{}, _t, _l, _c}}, _r}:
      True{}
    case _other:
      False{}

# does the chain start with a name and a `:`? An upper-case name counts when
# upper says so
def plan.typed(rest: Tree.Node, upper: Bool) -> Bool:
  match rest:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, _t, _l, _c}},
      Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TColon{}, _ct, _cl, _cc}}, _r}}:
      True{}
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TUpper{}, _t, _l, _c}},
      Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TColon{}, _ct, _cl, _cc}}, _r}}:
      upper
    case _other:
      False{}

# the chain's first token; a blank one when it does not start with a leaf
def plan.peek(rest: Tree.Node) -> Lex.Tok:
  match rest:
    case Tree.NCons{Tree.Leaf{tok}, _r}:
      tok
    case _other:
      Lex.Tok{Lex.TSpace{}, "", 0, 0}

# the chain after its first node
def plan.tail(rest: Tree.Node) -> Tree.Node:
  match rest:
    case Tree.NCons{_h, r}:
      r
    case _other:
      Tree.NNil{}

# the mode the rest is read in after a head that means nothing in this mode
def plan.skip(mode: Mode) -> Mode:
  match mode:
    case MBlock{}:
      MStop{}
    case MCtors{}:
      MStop{}
    case MCtor{}:
      MSig{}
    case MHead{}:
      MHead{}
    case MName{}:
      MSig{}
    case MSig{}:
      MTerm{}
    case MTele{kind}:
      MTele{kind}
    case MTeleType{kind}:
      MTeleType{kind}
    case MLhs{outer, kind}:
      MLhs{outer, kind}
    case MLhsType{outer}:
      MLhsType{outer}
    case MTerm{}:
      MTerm{}
    case MSkip{next}:
      next
    case MStop{}:
      MStop{}

# the mode the rest is read in after a leaf of kind k
def plan.lmode(mode: Mode, kk: Lex.TokKind, +rest: Tree.Node) -> Mode:
  match mode kk:
    case MHead{} Lex.TKey{}:
      MName{}
    case MTele{+kind} Lex.TOp{}:
      Bool.pick(Mode, plan.named(rest), MSkip{MTele{kind}}, MTele{kind})
    case MTele{kind} Lex.TColon{}:
      MTeleType{kind}
    case MTeleType{kind} Lex.TComma{}:
      MTele{kind}
    case MTeleType{+kind} Lex.TAll{}:
      Bool.pick(Mode, plan.typed(rest, False{}), MSkip{MTeleType{kind}}, MTeleType{kind})
    case MLhs{+outer, kind} Lex.TUpper{}:
      Bool.pick(Mode, plan.group(rest), MLhs{outer, KPat{}}, MLhs{outer, kind})
    case MLhs{+outer, kind} Lex.TDotted{}:
      Bool.pick(Mode, plan.group(rest), MLhs{outer, KPat{}}, MLhs{outer, kind})
    case MLhs{outer, _kind} Lex.TColon{}:
      MLhsType{outer}
    case MLhs{_outer, _kind} Lex.TEq{}:
      MTerm{}
    case MLhs{_outer, _kind} Lex.TBind{}:
      MTerm{}
    case MLhsType{_outer} Lex.TEq{}:
      MTerm{}
    case MLhsType{_outer} Lex.TBind{}:
      MTerm{}
    case MTerm{} Lex.TAll{}:
      Bool.pick(Mode, plan.typed(rest, True{}), MSkip{MTerm{}}, MTerm{})
    case MTerm{} Lex.TAmp{}:
      Bool.pick(Mode, plan.typed(rest, False{}), MSkip{MTerm{}}, MTerm{})
    case other _k:
      plan.skip(other)

# does a leaf of kind k record a binder?
def plan.rec(mode: Mode, kk: Lex.TokKind, +rest: Tree.Node) -> Bool:
  match mode kk:
    case MCtor{} Lex.TUpper{}:
      True{}
    case MName{} Lex.TName{}:
      True{}
    case MName{} Lex.TUpper{}:
      True{}
    case MName{} Lex.TDotted{}:
      True{}
    case MTele{_kind} Lex.TOp{}:
      plan.named(rest)
    case MTele{_kind} Lex.TName{}:
      True{}
    case MTele{_kind} Lex.TUpper{}:
      True{}
    case MTeleType{_kind} Lex.TAll{}:
      plan.typed(rest, False{})
    case MLhs{_outer, _kind} Lex.TUpper{}:
      Bool.not(plan.group(rest))
    case MLhs{_outer, _kind} Lex.TName{}:
      True{}
    case MTerm{} Lex.TName{}:
      plan.lam(rest)
    case MTerm{} Lex.TAll{}:
      plan.typed(rest, True{})
    case MTerm{} Lex.TAmp{}:
      plan.typed(rest, False{})
    case _other _k:
      False{}

# does the binder a leaf records go into the environment too? All do but an
# item's name and a constructor's, which the file's items hold
def plan.push(mode: Mode, kk: Lex.TokKind, rest: Tree.Node) -> Bool:
  match mode:
    case MCtor{}:
      False{}
    case MName{}:
      False{}
    case other:
      plan.rec(other, kk, rest)

# does a leaf of kind k use a name?
def plan.use(mode: Mode, kk: Lex.TokKind, +rest: Tree.Node) -> Bool:
  match mode kk:
    case MTeleType{_kind} Lex.TName{}:
      True{}
    case MTeleType{_kind} Lex.TUpper{}:
      True{}
    case MTeleType{_kind} Lex.TDotted{}:
      True{}
    case MLhs{_outer, _kind} Lex.TUpper{}:
      plan.group(rest)
    case MLhs{_outer, _kind} Lex.TDotted{}:
      plan.group(rest)
    case MLhsType{_outer} Lex.TName{}:
      True{}
    case MLhsType{_outer} Lex.TUpper{}:
      True{}
    case MLhsType{_outer} Lex.TDotted{}:
      True{}
    case MTerm{} Lex.TName{}:
      Bool.not(plan.lam(rest))
    case MTerm{} Lex.TUpper{}:
      True{}
    case MTerm{} Lex.TDotted{}:
      True{}
    case _other _k:
      False{}

# is a leaf of kind k the `=` or `<-` of a let, whose right side sees the
# names outside the let?
def plan.keep(mode: Mode, kk: Lex.TokKind) -> Bool:
  match mode kk:
    case MLhs{_outer, _kind} Lex.TEq{}:
      True{}
    case MLhs{_outer, _kind} Lex.TBind{}:
      True{}
    case MLhsType{_outer} Lex.TEq{}:
      True{}
    case MLhsType{_outer} Lex.TBind{}:
      True{}
    case _other _k:
      False{}

# the environment outside a let's left side
def plan.outer(mode: Mode) -> List<&2, Bind>:
  match mode:
    case MLhs{outer, _kind}:
      outer
    case MLhsType{outer}:
      outer
    case _other:
      []

# a binder at the next token, with the note its kind shows
def plan.ahead(tok: Lex.Tok, kind: BindKind, +note: String) -> Bind:
  match tok:
    case Lex.Tok{_k, t, l, c}:
      Bind{t, l, c, kind, note}

# the name of the next token, "" when there is none
def plan.ahead_name(tok: Lex.Tok) -> String:
  match tok:
    case Lex.Tok{_k, t, _l, _c}:
      t

# the binder a leaf records: its own name, or for `op name`, `@x:` and `&x:`
# the name after it. A telescope's binder notes its declaration
def plan.binder(mode: Mode, kk: Lex.TokKind, +tt: String, ll: U32, cc: U32, +rest: Tree.Node) -> Bind:
  match mode kk:
    case MCtor{} _k:
      Bind{tt, ll, cc, KCtor{}, ""}
    case MName{} _k:
      Bind{tt, ll, cc, KItem{}, ""}
    case MTele{kind} Lex.TOp{}:
      plan.ahead(plan.peek(rest), kind, tt ++ plan.ahead_name(plan.peek(rest)) ++ render(plan.tail(rest)))
    case MTele{kind} _k:
      Bind{tt, ll, cc, kind, "" ++ tt ++ render(rest)}
    case MTeleType{_kind} _k:
      plan.ahead(plan.peek(rest), KTypeVar{}, "")
    case MLhs{_outer, kind} _k:
      Bind{tt, ll, cc, kind, ""}
    case MTerm{} Lex.TName{}:
      Bind{tt, ll, cc, KLocal{}, ""}
    case MTerm{} _k:
      plan.ahead(plan.peek(rest), KTypeVar{}, "")
    case _other _k:
      Bind{tt, ll, cc, KLocal{}, ""}

# a binder onto the environment, when there is one
def plan.pushed(push: Bool, +bb: Bind, env: List<&2, Bind>) -> List<&2, Bind>:
  match push:
    case True{}:
      bb <> env
    case False{}:
      env

# a binder onto the output, when there is one
def plan.recorded(rec: Bool, +bb: Bind, out: Out) -> Out:
  match rec:
    case True{}:
      Out{binds, uses, scopes} = out
      Out{bb <> binds, uses, scopes}
    case False{}:
      out

# a use onto the output, when there is one
def plan.used(usd: Bool, +name: String, line: U32, col: U32, env: List<&2, Bind>, ns: Names, out: Out) -> Out:
  match usd:
    case True{}:
      out_of(use(name, line, col, env, ns, out))
    case False{}:
      out

# the environment the rest is read with after a leaf: the one outside a
# let's left side at its `=`, else this one with the leaf's binder on it
def plan.enter(
  keep: Bool,
  outer: List<&2, Bind>,
  push: Bool,
  +bb: Bind,
  env: List<&2, Bind>
) -> List<&2, Bind>:
  match keep:
    case True{}:
      outer
    case False{}:
      plan.pushed(push, bb, env)

# the mode a group's insides are read in; MStop when they mean nothing here
def plan.ginner(mode: Mode, +gt: String) -> Mode:
  match mode:
    case MSig{}:
      MTele{tele_kind(gt)}
    case MTeleType{_kind}:
      MTerm{}
    case MLhs{outer, _kind}:
      MLhs{outer, KPat{}}
    case MLhsType{_outer}:
      MTerm{}
    case MTerm{}:
      MTerm{}
    case _other:
      MStop{}

# the mode the rest is read in after a group
def plan.gnext(mode: Mode) -> Mode:
  match mode:
    case MSig{}:
      MTerm{}
    case MLhs{outer, _kind}:
      MLhs{outer, KPat{}}
    case other:
      plan.skip(other)

# do the names a group binds stay bound after it? A signature's parameters
# and a pattern's binders do
def plan.gkeeps(mode: Mode) -> Bool:
  match mode:
    case MSig{}:
      True{}
    case MLhs{_outer, _kind}:
      True{}
    case _other:
      False{}

# the mode a statement's header is read in
def plan.kmode(mode: Mode, sk: Tree.StmtKind, +env: List<&2, Bind>) -> Mode:
  match mode sk:
    case MBlock{} Tree.SDef{}:
      MHead{}
    case MBlock{} Tree.SLaw{}:
      MHead{}
    case MBlock{} Tree.SType{}:
      MHead{}
    case MBlock{} Tree.SImport{}:
      MStop{}
    case MBlock{} Tree.SCase{}:
      MLhs{env, KPat{}}
    case MBlock{} Tree.SFor{}:
      MLhs{env, KFor{}}
    case MBlock{} Tree.SLet{}:
      MLhs{env, KLocal{}}
    case MBlock{} Tree.STerm{}:
      MTerm{}
    case MCtors{} _sk:
      MCtor{}
    case _other _sk:
      MStop{}

# the mode a statement's body is read in
def plan.bmode(mode: Mode, sk: Tree.StmtKind) -> Mode:
  match mode sk:
    case MBlock{} Tree.SType{}:
      MCtors{}
    case MBlock{} Tree.SImport{}:
      MStop{}
    case MBlock{} _sk:
      MBlock{}
    case _other _sk:
      MStop{}

# is the scope recorded before a statement's header?
def plan.mark_head(mode: Mode, sk: Tree.StmtKind) -> Bool:
  match mode sk:
    case MBlock{} Tree.SCase{}:
      True{}
    case MBlock{} Tree.SFor{}:
      True{}
    case MBlock{} Tree.SLet{}:
      True{}
    case MBlock{} Tree.STerm{}:
      True{}
    case MCtors{} _sk:
      True{}
    case _other _sk:
      False{}

# is the scope recorded between a statement's header and its body? A def's is
def plan.mark_body(mode: Mode, sk: Tree.StmtKind) -> Bool:
  match mode sk:
    case MBlock{} Tree.SDef{}:
      True{}
    case _other _sk:
      False{}

# the scope recorded onto the output, when it is
def plan.marked(yes: Bool, line: U32, +env: List<&2, Bind>, out: Out) -> Out:
  match yes:
    case True{}:
      mark(line, env, out)
    case False{}:
      out

# does a statement close its scope for the statements after it? All but a
# let and a `for` in a block do
def plan.scoped(mode: Mode, sk: Tree.StmtKind) -> Bool:
  match mode sk:
    case MBlock{} Tree.SFor{}:
      False{}
    case MBlock{} Tree.SLet{}:
      False{}
    case _other _sk:
      True{}

# the mode the statements after a statement are read in
def plan.snext(mode: Mode) -> Mode:
  match mode:
    case MBlock{}:
      MBlock{}
    case MCtors{}:
      MCtors{}
    case other:
      plan.skip(other)

# the walk: one node in one mode, against an environment. It takes the node
# apart as far as its head, and the plan above says what the head does in
# this mode. Every recursive call is on a subtree (kids, body, gkids or
# rest), never on n itself
def walk(nn: Tree.Node, +mode: Mode, +env: List<&2, Bind>, +ns: Names, out: Out) -> W:
  match nn:
    case Tree.NCons{hd, +rest}:
      match hd:
        case Tree.Leaf{Lex.Tok{+k, +t, +l, +c}}:
          +keep = plan.keep(mode, k)
          +bb = plan.binder(mode, k, t, l, c, rest)
          +o1 = plan.recorded(plan.rec(mode, k, rest), bb, out)
          +o2 = plan.used(plan.use(mode, k, rest), t, l, c, env, ns, o1)
          +e2 = plan.enter(keep, plan.outer(mode), plan.push(mode, k, rest), bb, env)
          +r = walk(rest, plan.lmode(mode, k, rest), e2, ns, o2)
          W{Bool.pick(List<&2, Bind>, keep, env, env_of(r)), out_of(r)}
        case Tree.Group{Lex.Tok{_gk, gt, _gl, _gc}, gkids, _close}:
          +g = walk(gkids, plan.ginner(mode, gt), env, ns, out)
          walk(rest, plan.gnext(mode), Bool.pick(List<&2, Bind>, plan.gkeeps(mode), env_of(g), env), ns, out_of(g))
        case Tree.Stmt{+sk, +kids, body}:
          +h = walk(kids, plan.kmode(mode, sk, env), env, ns,
            plan.marked(plan.mark_head(mode, sk), Tree.line(kids), env, out))
          +b = walk(body, plan.bmode(mode, sk), env_of(h), ns,
            plan.marked(plan.mark_body(mode, sk), Tree.line(kids), env_of(h), out_of(h)))
          walk(rest, plan.snext(mode), Bool.pick(List<&2, Bind>, plan.scoped(mode, sk), env, env_of(h)), ns, out_of(b))
        case _other:
          walk(rest, plan.skip(mode), env, ns, out)
    case _other:
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

# a line's text without its indentation
def stripped(+text: String) -> String:
  String.from_list(lstrip(String.to_list(text)))

# a declaration carries its own note; anything else shows the line that
# bound it, which `text` gives only when it is asked for
def note_for(kind: BindKind, +note: String, text: Unit -> String) -> String:
  match kind:
    case KParam{}:
      note
    case KField{}:
      note
    case KTypeParam{}:
      note
    case other:
      text(Unit{})

# the lines from line `line` on, given the lines from line `at` on: a step
# forward from where the last binder was, not a walk from the first line
def annotate.ahead(+line: U32, +at: U32, cur: List<&2, String>) -> List<&2, String>:
  List.drop(&2, String, cur, U32.to_nat(U32.sub(line, at)))

# the first line of these, or ""
def annotate.head(+cur: List<&2, String>) -> String:
  Maybe.default(&2, String, List.head(&2, String, cur), "")

# a line read from the first, for a binder behind the last one
def annotate.back(lines: List<&2, String>, +line: U32) -> String:
  Maybe.default(&2, String, List.get(&2, String, lines, U32.to_nat(line)), "")

# every binder with its note filled. Binders come in source order, so the
# lines are read once, front to back, from where the last binder was (`cur`
# holds the lines from line `at` on); a binder behind that point reads its
# line from the start
def annotate.go(binds: List<&2, Bind>, +lines: List<&2, String>, +at: U32, +cur: List<&2, String>) -> List<&2, Bind>:
  match binds:
    case Nil{}:
      Nil{}
    case Con{Bind{name, +line, col, +kind, note}, rest}:
      +ahead = U32.is_ge(line, at)
      +here = Lazy.either(List<&2, String>, ahead, _u => annotate.ahead(line, at, cur), _v => cur)
      +text = Lazy.either(String, ahead, _u => annotate.head(here), _v => annotate.back(lines, line))
      Bind{name, line, col, kind, note_for(kind, note, _w => stripped(text))}
        <> annotate.go(rest, lines, Bool.pick(U32, ahead, line, at), here)

# every binder with its note filled
def annotate(binds: List<&2, Bind>, +lines: List<&2, String>) -> List<&2, Bind>:
  annotate.go(binds, lines, 0, lines)

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
