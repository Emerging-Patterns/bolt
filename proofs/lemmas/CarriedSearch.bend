# lemmas the proofs share: the searches that carry their test into the next
# call (a hit stops the walk) unfold, one cell at a time, to the pick between
# the head and the rest they were before they stopped early
import Base
import ../../src/syntax/lex.bend as Lex
import ../../src/syntax/tree.bend as Tree
import ../../src/config.bend as Config
import ../../src/rules/digest.bend as Digest
import ../../src/rules/imports.bend as Imports
import ../../src/rules/calls.bend as Calls
import ../../src/syntax/bind.bend as Bind

# a hit carried into set_level's walk is its answer
law cs.set_level.some:
  for sets: List<&2, Config.LevelSet>
  for +name: String
  for +x: Config.Level
  {Config.set_level.go(sets, name, Some{x}) == Some{x} : Maybe<&2, Config.Level>}

def cs.set_level.some(sets, _name, _x):
  match sets:
    case Nil{}:
      {==}
    case Con{h, r}:
      match h:
        case Config.LevelSet{n, l}:
          {==}

# set_level's walk past a test: the pick it stands for
law cs.set_level.pick:
  for b: Bool
  for +sets: List<&2, Config.LevelSet>
  for +name: String
  for +l: Config.Level
  {Config.set_level.go(sets, name, Bool.pick(Maybe<&2, Config.Level>, b, Some{l}, None{}))
    == Bool.pick(Maybe<&2, Config.Level>, b, Some{l}, Config.set_level.go(sets, name, None{}))
    : Maybe<&2, Config.Level>}

def cs.set_level.pick(b, sets, name, l):
  match b:
    case True{}:
      cs.set_level.some(sets, name, l)
    case False{}:
      {==}

# set_level on a setting: the setting's level when it names the name, else
# the rest's
law cs.set_level:
  for +n: String
  for +l: Config.Level
  for +sets: List<&2, Config.LevelSet>
  for +name: String
  {Config.set_level(Config.LevelSet{n, l} <> sets, name)
    == Bool.pick(Maybe<&2, Config.Level>, String.eq(n, name), Some{l}, Config.set_level(sets, name))
    : Maybe<&2, Config.Level>}

def cs.set_level(n, l, sets, name):
  cs.set_level.pick(String.eq(n, name), sets, name, l)

# a hit carried into alias_path's walk is its answer
law cs.alias_path.some:
  for as: List<&2, Digest.Alias>
  for +name: String
  for +x: String
  {Digest.alias_path.go(as, name, Some{x}) == Some{x} : Maybe<&2, String>}

def cs.alias_path.some(as, _name, _x):
  match as:
    case Nil{}:
      {==}
    case Con{h, r}:
      match h:
        case Digest.Alias{n, p}:
          {==}

# alias_path's walk past a test: the pick it stands for
law cs.alias_path.pick:
  for b: Bool
  for +as: List<&2, Digest.Alias>
  for +name: String
  for +p: String
  {Digest.alias_path.go(as, name, Bool.pick(Maybe<&2, String>, b, Some{p}, None{}))
    == Bool.pick(Maybe<&2, String>, b, Some{p}, Digest.alias_path.go(as, name, None{})) : Maybe<&2, String>}

def cs.alias_path.pick(b, as, name, p):
  match b:
    case True{}:
      cs.alias_path.some(as, name, p)
    case False{}:
      {==}

# alias_path on an alias: its path when it is the name, else the rest's
law cs.alias_path:
  for +n: String
  for +p: String
  for +as: List<&2, Digest.Alias>
  for +name: String
  {Digest.alias_path(Digest.Alias{n, p} <> as, name)
    == Bool.pick(Maybe<&2, String>, String.eq(n, name), Some{p}, Digest.alias_path(as, name)) : Maybe<&2, String>}

def cs.alias_path(n, p, as, name):
  cs.alias_path.pick(String.eq(n, name), as, name, p)

# a hit carried into find's walk is its answer
law cs.find.some:
  for env: List<&2, Bind.Bind>
  for +name: String
  for +x: Bind.Bind
  {Bind.find.go(env, name, Some{x}) == Some{x} : Maybe<&2, Bind.Bind>}

def cs.find.some(env, _name, _x):
  match env:
    case Nil{}:
      {==}
    case Con{h, r}:
      match h:
        case Bind.Bind{n, l, c, k, note}:
          {==}

# find's walk past a test: the pick it stands for
law cs.find.pick:
  for b: Bool
  for +env: List<&2, Bind.Bind>
  for +name: String
  for +x: Bind.Bind
  {Bind.find.go(env, name, Bool.pick(Maybe<&2, Bind.Bind>, b, Some{x}, None{}))
    == Bool.pick(Maybe<&2, Bind.Bind>, b, Some{x}, Bind.find.go(env, name, None{})) : Maybe<&2, Bind.Bind>}

def cs.find.pick(b, env, name, x):
  match b:
    case True{}:
      cs.find.some(env, name, x)
    case False{}:
      {==}

# find on a binder: it when it binds the name, else the rest's
law cs.find:
  for +n: String
  for +l: U32
  for +c: U32
  for +k: Bind.BindKind
  for +note: String
  for +env: List<&2, Bind.Bind>
  for +name: String
  {Bind.find(Bind.Bind{n, l, c, k, note} <> env, name)
    == Bool.pick(Maybe<&2, Bind.Bind>, String.eq(n, name), Some{Bind.Bind{n, l, c, k, note}}, Bind.find(env, name))
    : Maybe<&2, Bind.Bind>}

def cs.find(n, l, c, k, note, env, name):
  cs.find.pick(String.eq(n, name), env, name, Bind.Bind{n, l, c, k, note})

# a hit carried into params.of's walk is its answer
law cs.params.some:
  for sig: Tree.Node
  for +x: Tree.Node
  {Calls.params.of.go(sig, Some{x}) == x : Tree.Node}

def cs.params.some(sig, _x):
  match sig:
    case Tree.NCons{h, r}:
      match h:
        case Tree.Group{o, kids, cl}:
          match o:
            case Lex.Tok{k, t, l, c}:
              {==}
        case Tree.Leaf{y}: {==}
        case Tree.Stmt{y, z, w}: {==}
        case Tree.NNil{}: {==}
        case Tree.NCons{y, z}: {==}
    case Tree.Leaf{y}: {==}
    case Tree.Group{y, z, w}: {==}
    case Tree.Stmt{y, z, w}: {==}
    case Tree.NNil{}: {==}

# params.of's walk past a test: the pick it stands for
law cs.params.pick:
  for b: Bool
  for +sig: Tree.Node
  for +kids: Tree.Node
  {Calls.params.of.go(sig, Bool.pick(Maybe<&2, Tree.Node>, b, Some{kids}, None{}))
    == Bool.pick(Tree.Node, b, kids, Calls.params.of.go(sig, None{})) : Tree.Node}

def cs.params.pick(b, sig, kids):
  match b:
    case True{}:
      cs.params.some(sig, kids)
    case False{}:
      {==}

# params.of on a group: its kids when it is a `(` group, else the rest's
law cs.params.of:
  for +k: Lex.TokKind
  for +o: String
  for +l: U32
  for +c: U32
  for +kids: Tree.Node
  for +close: Maybe<&2, Lex.Tok>
  for +rest: Tree.Node
  {Calls.params.of(Tree.NCons{Tree.Group{Lex.Tok{k, o, l, c}, kids, close}, rest})
    == Bool.pick(Tree.Node, String.eq(o, "("), kids, Calls.params.of(rest)) : Tree.Node}

def cs.params.of(_k, o, _l, _c, kids, _close, rest):
  cs.params.pick(String.eq(o, "("), rest, kids)

# a hit carried into type_head's walk is its answer
law cs.head.some:
  for pp: Tree.Node
  for +after: Bool
  for +s: String
  {Calls.type_head.go(pp, after, Some{s}) == s : String}

def cs.head.some(pp, _after, _s):
  match pp:
    case Tree.NCons{h, r}: {==}
    case Tree.Leaf{y}: {==}
    case Tree.Group{y, z, w}: {==}
    case Tree.Stmt{y, z, w}: {==}
    case Tree.NNil{}: {==}

# type_head's walk past a test: the pick it stands for
law cs.head.pick:
  for b: Bool
  for +pp: Tree.Node
  for +after: Bool
  for +s: String
  {Calls.type_head.go(pp, after, Bool.pick(Maybe<&2, String>, b, Some{s}, None{}))
    == Bool.pick(String, b, s, Calls.type_head.go(pp, after, None{})) : String}

def cs.head.pick(b, pp, after, s):
  match b:
    case True{}:
      cs.head.some(pp, after, s)
    case False{}:
      {==}

# type_head on a node: its text when the colon is behind and it is
# capitalized, else the rest's
law cs.type_head:
  for +h: Tree.Node
  for +rest: Tree.Node
  for +after: Bool
  {Calls.type_head(Tree.NCons{h, rest}, after)
    == Bool.pick(String, Bool.and(after, Calls.kind.leaf(~Calls.kind.upper, h)), Calls.leaf.text(h),
      Calls.type_head(rest, Bool.or(after, Calls.kind.leaf(~Calls.kind.colon, h)))) : String}

def cs.type_head(h, rest, after):
  cs.head.pick(Bool.and(after, Calls.kind.leaf(~Calls.kind.upper, h)), rest,
    Bool.or(after, Calls.kind.leaf(~Calls.kind.colon, h)), Calls.leaf.text(h))
