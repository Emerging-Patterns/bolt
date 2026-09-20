# bolt/rules/calls: what the recursion rules (pick, strict, tail, concat,
# index) share. A file's defs, each with its name, its signature and its body;
# a call's arguments; whether a def calls itself; its parameters, and the type
# of the one it walks; and whether it is exempt (a law or a proof never runs).
import Base
import ../../syntax/lex.bend as Lex
import ../../syntax/tree.bend as Tree
import ../../syntax/bind.bend as Bind
import ../../lazy/lazy.bend as Lazy

# a def: its name, its own tokens (the signature) and the statements under it
type Def is Data:
  Def{name: String, sig: Tree.Node, body: Tree.Node}

# a def with a name joins the others; one without (half-written) does not
def defs.push(m: Maybe<&2, String>, sig: Tree.Node, body: Tree.Node, acc: List<&2, Def>) -> List<&2, Def>:
  match m:
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

# the arguments of a group, split at its top-level commas (each a chain)
def args.go(kids: Tree.Node, cur: Tree.Node, acc: List<&2, Tree.Node>) -> List<&2, Tree.Node>:
  match kids:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TComma{}, t, l, c}}, rest}:
      args.go(rest, Tree.NNil{}, Tree.reverse(cur, Tree.NNil{}) <> acc)
    case Tree.NCons{h, rest}:
      args.go(rest, Tree.NCons{h, cur}, acc)
    case other:
      List.reverse(&2, Tree.Node, Tree.reverse(cur, Tree.NNil{}) <> acc)

# the arguments of a group
def args(kids: Tree.Node) -> List<&2, Tree.Node>:
  args.go(kids, Tree.NNil{}, [])

# the nth argument, or nothing
def arg(as: List<&2, Tree.Node>, n: Nat) -> Tree.Node:
  match as n:
    case Con{h, t} 0n:
      h
    case Con{h, t} 1n+p:
      arg(t, p)
    case Nil{} m:
      Tree.NNil{}

# does the name appear anywhere under the node?
def mentions(n: Tree.Node, +name: String) -> Bool:
  match n:
    case Tree.Leaf{Lex.Tok{k, +t, l, c}}:
      String.eq(t, name)
    case Tree.Group{open, kids, close}:
      mentions(kids, name)
    case Tree.Stmt{kind, kids, body}:
      +a = mentions(kids, name)
      +b = mentions(body, name)
      Bool.or(a, b)
    case Tree.NNil{}:
      False{}
    case Tree.NCons{h, t}:
      +a = mentions(h, name)
      +b = mentions(t, name)
      Bool.or(a, b)

# is there a call of the name, `name(..)`, anywhere under the node?
def calls(n: Tree.Node, +name: String) -> Bool:
  match n:
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
def param_name(p: Tree.Node) -> String:
  match p:
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
def has_colon(p: Tree.Node) -> Bool:
  match p:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TColon{}, t, l, c}}, rest}:
      True{}
    case Tree.NCons{h, rest}:
      has_colon(rest)
    case other:
      False{}

# a live parameter: typed, and neither erased (`-A: Type`) nor a template
# (`~f: A -> B`); a bare quantity name (`a` in `List.get(a, ..)`) is not one
def is_live(p: Tree.Node) -> Bool:
  match p:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TOp{}, +t, l, c}}, rest}:
      Bool.and(Bool.not(Bool.or(String.eq(t, "-"), String.eq(t, "~"))), has_colon(rest))
    case other:
      has_colon(other)

# the head of a parameter's type: the first capitalized name after the colon
# (`List` in `+xs: +List<A>`), "" for none
def type_head(p: Tree.Node, +after: Bool) -> String:
  match p:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TColon{}, t, l, c}}, rest}:
      type_head(rest, True{})
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TUpper{}, +t, l, c}}, rest}:
      +more = type_head(rest, after)
      Bool.pick(String, after, t, more)
    case Tree.NCons{h, rest}:
      type_head(rest, after)
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

# does the signature return a proof, `-> {a == b : T}`?
def returns_proof(sig: Tree.Node) -> Bool:
  match sig:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TArrow{}, t, l, c}}, Tree.NCons{g, rest}}:
      +more = returns_proof(rest)
      Bool.or(Tree.opens(g, "{"), more)
    case Tree.NCons{h, rest}:
      returns_proof(rest)
    case other:
      False{}

# a law file, a proof file, or a def that returns a proof: none of it runs,
# so its cost does not matter
def exempt(+path: String, sig: Tree.Node) -> Bool:
  Bool.or(Bool.or(String.ends_with(path, "LAWS.bend"), String.ends_with(path, "PROOF.bend")), returns_proof(sig))
