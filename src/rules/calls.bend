# src/rules/calls: what the recursion rules (pick, strict, tail, concat,
# index) share. A file's defs, each with its name, its signature and its body;
# a call's arguments; whether a def calls itself; its parameters, and the type
# of the one it walks; and whether it is exempt (a law or a proof never runs,
# and a def with no type fills a law: it is a proof).
import Base
import ../paths.bend as Paths
import ../syntax/lex.bend as Lex
import ../syntax/tree.bend as Tree
import ../syntax/bind.bend as Bind
import ../lazy/lazy.bend as Lazy

# a def: its name, its own tokens (the signature) and the statements under it
type Def is Data:
  Def{name: String, sig: Tree.Node, body: Tree.Node}

# a def with a name joins the others; one without (half-written) does not
def defs.push(mm: Maybe<&2, String>, sig: Tree.Node, body: Tree.Node, acc: List<&2, Def>) -> List<&2, Def>:
  match mm:
    case None{}:
      acc
    case Some{name}:
      Def{name, sig, body} <> acc

# the defs of a parsed source, in order
def defs(root: Tree.Node) -> List<&2, Def>:
  match root:
    case Tree.NCons{Tree.Stmt{Tree.SDef{}, +kids, body}, rest}:
      defs.push(Bind.declared(kids), kids, body, defs(rest))
    case Tree.NCons{h, rest}:
      defs(rest)
    case other:
      Nil{}

# a leaf's kind, none for anything else: kind tests read this, never a text
def leaf.kind(nn: Tree.Node) -> Maybe<&2, Lex.TokKind>:
  match nn:
    case Tree.Leaf{Lex.Tok{k, t, l, c}}:
      Some{k}
    case other:
      None{}

# a kind test on a kind, when there is one
def kind.of(~test: Lex.TokKind -> Bool, mm: Maybe<&2, Lex.TokKind>) -> Bool:
  match mm:
    case None{}:
      False{}
    case Some{k}:
      test(k)

# a leaf of this kind?
def kind.leaf(~test: Lex.TokKind -> Bool, nn: Tree.Node) -> Bool:
  kind.of(~test, leaf.kind(nn))

# a `:`
def kind.colon(kk: Lex.TokKind) -> Bool:
  match kk:
    case Lex.TColon{}:
      True{}
    case other:
      False{}

# a capitalized name
def kind.upper(kk: Lex.TokKind) -> Bool:
  match kk:
    case Lex.TUpper{}:
      True{}
    case other:
      False{}

# `->`
def kind.arrow(kk: Lex.TokKind) -> Bool:
  match kk:
    case Lex.TArrow{}:
      True{}
    case other:
      False{}

# a plain operator (`-`, `~`, `+`)
def kind.oper(kk: Lex.TokKind) -> Bool:
  match kk:
    case Lex.TOp{}:
      True{}
    case other:
      False{}

# a leaf's text, "" for anything else
def leaf.text(nn: Tree.Node) -> String:
  match nn:
    case Tree.Leaf{Lex.Tok{k, t, l, c}}:
      t
    case other:
      ""

# the arguments of a group, split at its top-level commas (each a chain)
def args.go(kids: Tree.Node, +cur: Tree.Node, +acc: List<&2, Tree.Node>) -> List<&2, Tree.Node>:
  match kids:
    case Tree.NCons{+h, +rest}:
      Lazy.either(List<&2, Tree.Node>, kind.leaf(~Lex.is_comma, h),
        _u => args.go(rest, Tree.NNil{}, Tree.reverse(cur, Tree.NNil{}) <> acc),
        _v => args.go(rest, Tree.NCons{h, cur}, acc))
    case other:
      List.reverse(&2, Tree.Node, Tree.reverse(cur, Tree.NNil{}) <> acc)

# the arguments of a group
def args(kids: Tree.Node) -> List<&2, Tree.Node>:
  args.go(kids, Tree.NNil{}, [])

# the nth argument, or nothing
def arg(as: List<&2, Tree.Node>, nn: Nat) -> Tree.Node:
  match as nn:
    case Con{h, t} 0n:
      h
    case Con{h, t} 1n+p:
      arg(t, p)
    case Nil{} m:
      Tree.NNil{}

# is there a call of the name, `name(..)`, anywhere under the node?
def calls(nn: Tree.Node, +name: String) -> Bool:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, +t, l, c}}, Tree.NCons{Tree.Group{Lex.Tok{_, +o, _, _}, kids, _}, rest}}:
      +a = calls(kids, name)
      +b = calls(rest, name)
      Bool.or(Bool.and(String.eq(o, "("), String.eq(t, name)), Bool.or(a, b))
    case Tree.Group{open, kids, close}:
      calls(kids, name)
    case Tree.Stmt{kind, kids, body}:
      +a = calls(kids, name)
      +b = calls(body, name)
      Bool.or(a, b)
    case Tree.NCons{h, t}:
      +a = calls(h, name)
      +b = calls(t, name)
      Bool.or(a, b)
    case other:
      False{}

# the kids of a signature's first `(` group: the parameters
def params.of(sig: Tree.Node) -> Tree.Node:
  match sig:
    case Tree.NCons{Tree.Group{Lex.Tok{k, +o, l, c}, +kids, close}, rest}:
      +more = params.of(rest)
      Bool.pick(Tree.Node, String.eq(o, "("), kids, more)
    case Tree.NCons{h, rest}:
      params.of(rest)
    case other:
      Tree.NNil{}

# a def's parameters, each its chain up to a comma (`+xs: List<&2, U32>`)
def params(sig: Tree.Node) -> List<&2, Tree.Node>:
  args(params.of(sig))

# a parameter's name: its first lowercase name before the colon ("" for a
# type parameter like `-A: Type`)
def param_name(pp: Tree.Node) -> String:
  match pp:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, t, l, c}}, rest}:
      t
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TColon{}, t, l, c}}, rest}:
      ""
    case Tree.NCons{h, rest}:
      param_name(rest)
    case other:
      ""

def names.go(ps: List<&2, Tree.Node>, acc: List<&2, String>) -> List<&2, String>:
  match ps:
    case Nil{}:
      List.reverse(&2, String, acc)
    case Con{p, rest}:
      names.go(rest, param_name(p) <> acc)

# the names of a def's parameters
def names(sig: Tree.Node) -> List<&2, String>:
  names.go(params(sig), [])

# does a chain hold a top-level colon?
def has_colon(pp: Tree.Node) -> Bool:
  match pp:
    case Tree.NCons{h, rest}:
      Lazy.or_else(kind.leaf(~kind.colon, h), _u => has_colon(rest))
    case other:
      False{}

# does the chain open with a `-` or `~` operator?
def is_live.sign(pp: Tree.Node) -> Bool:
  match pp:
    case Tree.NCons{+h, rest}:
      +t = leaf.text(h)
      Bool.and(kind.leaf(~kind.oper, h), Bool.or(String.eq(t, "-"), String.eq(t, "~")))
    case other:
      False{}

# a live parameter: typed, and neither erased (`-A: Type`) nor a template
# (`~f: A -> B`); a bare quantity name (`a` in `List.get(a, ..)`) is not one
def is_live(+pp: Tree.Node) -> Bool:
  Bool.and(Bool.not(is_live.sign(pp)), has_colon(pp))

# the head of a parameter's type: the first capitalized name after the colon
# (`List` in `+xs: +List<A>`), "" for none
def type_head(pp: Tree.Node, +after: Bool) -> String:
  match pp:
    case Tree.NCons{+h, rest}:
      +more = type_head(rest, Bool.or(after, kind.leaf(~kind.colon, h)))
      Bool.pick(String, Bool.and(after, kind.leaf(~kind.upper, h)), leaf.text(h), more)
    case other:
      ""

def walked.go(ps: List<&2, Tree.Node>, found: Maybe<&2, String>) -> String:
  match ps found:
    case Con{+p, rest} None{}:
      walked.go(rest, Lazy.stop(Maybe<&2, String>, Bool.not(is_live(p)), None{},
        _u => Some{type_head(p, False{})}))
    case Con{p, rest} Some{t}:
      t
    case Nil{} Some{t}:
      t
    case Nil{} None{}:
      ""

# the type head of the first live parameter: the one a self-call must shrink
def walked(sig: Tree.Node) -> String:
  walked.go(params(sig), None{})

# does the def walk a list or a string (its first live parameter's type)?
def seq(sig: Tree.Node) -> Bool:
  +h = walked(sig)
  Bool.or(String.eq(h, "List"), String.eq(h, "String"))

# a `{` group after the arrow, or a proof further on
def returns_proof.or(+brace: Bool, more: Bool) -> Bool:
  Bool.or(brace, more)

# does the signature return a proof, `-> {a == b : T}`?
def returns_proof(sig: Tree.Node) -> Bool:
  match sig:
    case Tree.NCons{h, +rest}:
      match rest:
        case Tree.NCons{+g, r2}:
          Lazy.either(Bool, kind.leaf(~kind.arrow, h), _u => returns_proof.or(Tree.opens(g, "{"), returns_proof(r2)),
            _v => returns_proof(rest))
        case _r:
          returns_proof(rest)
    case other:
      False{}

# does a chain hold a top-level `->`?
def has_arrow(pp: Tree.Node) -> Bool:
  match pp:
    case Tree.NCons{h, rest}:
      Lazy.or_else(kind.leaf(~kind.arrow, h), _u => has_arrow(rest))
    case other:
      False{}

# does the signature write a type: a `:` among its parameters, or a `->`?
def typed(+sig: Tree.Node) -> Bool:
  Lazy.or_else(has_colon(params.of(sig)), _u => has_arrow(sig))

# is the def a proof? One that returns a proof (`-> {a == b : T}`), or one
# written with no type at all (`def f(x, y):`), which is how Bend fills the
# law named f
def proof(+sig: Tree.Node) -> Bool:
  Bool.or(returns_proof(sig), Bool.not(typed(sig)))

# a law file, a proof file, or a def that is a proof: none of it runs, so its
# cost does not matter
def exempt(+path: String, sig: Tree.Node) -> Bool:
  Bool.or(Paths.is_law_file(path), proof(sig))
