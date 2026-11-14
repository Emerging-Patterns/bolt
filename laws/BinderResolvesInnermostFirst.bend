# The binder resolves a use to the innermost binder, then a file item, then an
# alias qualifier, else free.
import Base
import ../src/syntax/lex.bend as Lex
import ../src/syntax/tree.bend as Tree
import ../src/syntax/bind.bend as Bind

# the binder's resolution (laws/BinderResolvesInnermostFirst.bend), written apart from bind.bend. The
# environment lists the binders in scope innermost first. A use of a name
# refers to the first binder of that name there; with none, to an item of
# the file of that name; with none, when the name has a dot and its part
# before the first dot is an import alias, to the rest after that dot behind
# the alias; else to nothing the file knows.

# the binders of a name, in the environment's order
def res.all(env: List<&2, Bind.Bind>, +name: String) -> List<&2, Bind.Bind>:
  match env:
    case Nil{}:
      []
    case Con{Bind.Bind{+n, l, c, k, note}, t}:
      +more = res.all(t, name)
      Bool.pick(List<&2, Bind.Bind>, String.eq(n, name), Bind.Bind{n, l, c, k, note} <> more, more)

# a name's part before its first dot: all of it when it has none
def res.before(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+h, t}:
      +more = res.before(t)
      Bool.pick(String, Char.is_eq(h, '.'), SNil{}, SCon{h, more})

# a name's part after its first dot, when it has one
def res.after(s: String) -> Maybe<&2, String>:
  match s:
    case SNil{}:
      None{}
    case SCon{+h, +t}:
      +more = res.after(t)
      Bool.pick(Maybe<&2, String>, Char.is_eq(h, '.'), Some{t}, more)

# a name no binder holds and no item has: behind an alias when it has a dot
# and the part before is one of the aliases, else free
def res.qual(after: Maybe<&2, String>, +before: String, als: List<&2, String>) -> Bind.Target:
  match after:
    case None{}:
      Bind.TFree{}
    case Some{rest}:
      Bool.pick(Bind.Target, List.contains(~String, ~String.eq, als, before), Bind.TQual{before, rest}, Bind.TFree{})

# what a name refers to once the innermost binder of it, if any, is found
def res.found(m: Maybe<&2, Bind.Bind>, +name: String, its: List<&2, String>, als: List<&2, String>) -> Bind.Target:
  match m:
    case Some{Bind.Bind{_n, l, c, _k, _note}}:
      Bind.TLocal{l, c}
    case None{}:
      Bool.pick(Bind.Target, List.contains(~String, ~String.eq, its, name), Bind.TItem{name},
        res.qual(res.after(name), res.before(name), als))

# what a name refers to, against the binders in scope and the file's items
# and aliases
def res.spec(env: List<&2, Bind.Bind>, +name: String, its: List<&2, String>, als: List<&2, String>) -> Bind.Target:
  res.found(List.head(&2, Bind.Bind, res.all(env, name)), name, its, als)

# LAW: the binder resolves a name to the innermost binder of it, else an
# item of the file, else an alias qualifier, else free: whatever the
# environment, the name, the items and the aliases. The binder asks the
# index of the items, which answers as a scan of them does
# (laws/BinderIndexFindsItems.bend)
law resolves:
  for +env: List<&2, Bind.Bind>
  for +name: String
  for +its: List<&2, String>
  for +als: List<&2, String>
  {Bind.resolve(env, name, Bind.Names{its, als, Bind.index(its)}) == res.spec(env, name, its, als) : Bind.Target}

# LAW: the walk records each use it reads with that target, and changes
# neither the environment nor anything else it has gathered
law uses:
  for +name: String
  for +line: U32
  for +col: U32
  for +env: List<&2, Bind.Bind>
  for +its: List<&2, String>
  for +als: List<&2, String>
  for +binds: List<&2, Bind.Bind>
  for +us: List<&2, Bind.Use>
  for +scopes: List<&2, Bind.Scope>
  {Bind.use(name, line, col, env, Bind.Names{its, als, Bind.index(its)}, Bind.Out{binds, us, scopes})
    == Bind.W{env, Bind.Out{binds, Bind.Use{name, line, col, res.spec(env, name, its, als)} <> us, scopes}} : Bind.W}

# the environment the walk threads (laws/BinderResolvesInnermostFirst.bend): what makes the first binder
# of a name in it the innermost one in scope. The walk only ever puts binders
# in front of the environment it was given, so a binder met later, further
# in, stands before the ones around it; binders in front shadow the ones
# behind; and a scope, once left, gives back the environment it was entered
# with: a statement other than a let or a `for` is such a scope for the
# statements after it, and a group for the terms after it, while a let or a
# `for` scopes over the rest of its block.

# LAW: whatever the walk reads, in whatever mode, the environment it leaves is
# the one it was given with binders put in front
law extends:
  for +n: Tree.Node
  for +mode: Bind.Mode
  for +env: List<&2, Bind.Bind>
  for +ns: Bind.Names
  for +out: Bind.Out
  exs ext: List<&2, Bind.Bind>
  {Bind.env_of(Bind.walk(n, mode, env, ns, out)) == List.append(&2, Bind.Bind, ext, env) : List<&2, Bind.Bind>}

# the first binder found, else the other
def res.first(m: Maybe<&2, Bind.Bind>, other: Maybe<&2, Bind.Bind>) -> Maybe<&2, Bind.Bind>:
  match m:
    case Some{b}:
      Some{b}
    case None{}:
      other

# LAW: binders put in front shadow the ones behind: the first binder of a
# name is the first of those in front, else the first of those behind
law shadows:
  for +ext: List<&2, Bind.Bind>
  for +env: List<&2, Bind.Bind>
  for +name: String
  {List.head(&2, Bind.Bind, res.all(List.append(&2, Bind.Bind, ext, env), name))
    == res.first(List.head(&2, Bind.Bind, res.all(ext, name)), List.head(&2, Bind.Bind, res.all(env, name)))
    : Maybe<&2, Bind.Bind>}

# does a statement of this kind close its scope for the statements after it?
# All but a let and a `for` do
def scoped(k: Tree.StmtKind) -> Bool:
  match k:
    case Tree.SLet{}:
      False{}
    case Tree.SFor{}:
      False{}
    case _other:
      True{}

# LAW: the statements after a def, law, type, import, case or term statement
# are read with the environment it was entered with
law restores:
  for +k: Tree.StmtKind
  for +kids: Tree.Node
  for +body: Tree.Node
  for +rest: Tree.Node
  for +env: List<&2, Bind.Bind>
  for +ns: Bind.Names
  for +out: Bind.Out
  for e: {scoped(k) == True{} : Bool}
  exs o: Bind.Out
  {Bind.walk(Tree.NCons{Tree.Stmt{k, kids, body}, rest}, Bind.MBlock{}, env, ns, out)
    == Bind.walk(rest, Bind.MBlock{}, env, ns, o) : Bind.W}

# LAW: the statements after a let or a `for` are read with the environment it
# was entered with, its binders put in front
law lets:
  for +k: Tree.StmtKind
  for +kids: Tree.Node
  for +body: Tree.Node
  for +rest: Tree.Node
  for +env: List<&2, Bind.Bind>
  for +ns: Bind.Names
  for +out: Bind.Out
  for e: {scoped(k) == False{} : Bool}
  exs ext: List<&2, Bind.Bind>
  exs o: Bind.Out
  {Bind.walk(Tree.NCons{Tree.Stmt{k, kids, body}, rest}, Bind.MBlock{}, env, ns, out)
    == Bind.walk(rest, Bind.MBlock{}, List.append(&2, Bind.Bind, ext, env), ns, o) : Bind.W}

# LAW: the terms after a group are read with the environment it was entered
# with: a lambda inside it binds only inside it
law groups:
  for +open: Lex.Tok
  for +gkids: Tree.Node
  for +close: Maybe<&2, Lex.Tok>
  for +rest: Tree.Node
  for +env: List<&2, Bind.Bind>
  for +ns: Bind.Names
  for +out: Bind.Out
  exs o: Bind.Out
  {Bind.walk(Tree.NCons{Tree.Group{open, gkids, close}, rest}, Bind.MTerm{}, env, ns, out)
    == Bind.walk(rest, Bind.MTerm{}, env, ns, o) : Bind.W}
