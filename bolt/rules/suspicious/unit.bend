# rule unit: a multiply or divide by the literal one (`1`, `1n`, `1.0`) on a
# step that actually recurses. `*` and `/` inside `(e : T)` are `T.mul` and
# `T.div`; bare, they are `Nat`. Either form, and a direct `Nat.mul` /
# `U32.mul` / `F32.mul` or `.div`, does nothing when an operand is one
# (`/` only when the divisor is). Drop the operation. Any other factor or
# divisor is left alone, and so is a base case or a def that does not call
# itself. Laws and proofs do not run.
import Base
import ../../src.bend as Src
import ../../finding.bend as F
import ../../../syntax/lex.bend as Lex
import ../../../syntax/tree.bend as Tree
import ../calls.bend as Calls
import ../../../lazy/lazy.bend as Lazy

# is the text the literal one?
def one_text(+tt: String) -> Bool:
  Bool.or(String.eq(tt, "1"), Bool.or(String.eq(tt, "1n"), String.eq(tt, "1.0")))

# is the kind a number token?
def num_kind(kk: Lex.TokKind) -> Bool:
  match kk:
    case Lex.TNum{}:
      True{}
    case other:
      False{}

# a token that is the literal one
def one_tok(tok: Lex.Tok) -> Bool:
  Lex.Tok{+k, +t, l, c} = tok
  Bool.and(num_kind(k), one_text(t))

# the maybe holds the literal one
def one_maybe(mm: Maybe<&2, Lex.Tok>) -> Bool:
  match mm:
    case None{}:
      False{}
    case Some{tok}:
      one_tok(tok)

# `*` with one on either side, or `/` with one as the divisor
def identity(+op: String, prev: Maybe<&2, Lex.Tok>, nxt: Maybe<&2, Lex.Tok>) -> Bool:
  +star = String.eq(op, "*")
  +slash = String.eq(op, "/")
  +left = one_maybe(prev)
  +right = one_maybe(nxt)
  Bool.or(Bool.and(star, Bool.or(left, right)), Bool.and(slash, right))

# the literal the finding points at: the divisor, else the factor
def which(+op: String, prev: Maybe<&2, Lex.Tok>, +nxt: Maybe<&2, Lex.Tok>) -> Maybe<&2, Lex.Tok>:
  +right = one_maybe(nxt)
  Bool.pick(Maybe<&2, Lex.Tok>, Bool.or(String.eq(op, "/"), right), nxt, prev)

# a finding on that literal
def cite(mm: Maybe<&2, Lex.Tok>, +path: String) -> List<&2, F.Finding>:
  match mm:
    case None{}:
      Nil{}
    case Some{Lex.Tok{k, +t, l, c}}:
      [F.Finding{path, l, c, U32.from_nat(String.length(t)), "unit",
        t ++ " is a multiply or divide by one, which changes nothing; drop the operation."}]

# an argument that is exactly the literal one
def arg_one(aa: Tree.Node) -> Maybe<&2, Lex.Tok>:
  match aa:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TNum{}, +t, l, c}}, Tree.NNil{}}:
      Bool.pick(Maybe<&2, Lex.Tok>, one_text(t), Some{Lex.Tok{Lex.TNum{}, t, l, c}}, None{})
    case other:
      None{}

# the last argument, when it is the literal one
def last_one(as: List<&2, Tree.Node>) -> Maybe<&2, Lex.Tok>:
  match as:
    case Nil{}:
      None{}
    case Con{h, Nil{}}:
      arg_one(h)
    case Con{h, rest}:
      last_one(rest)

# every argument that is the literal one
def any_one(as: List<&2, Tree.Node>, +path: String) -> List<&2, F.Finding>:
  match as:
    case Nil{}:
      Nil{}
    case Con{h, rest}:
      List.append(&2, F.Finding, cite(arg_one(h), path), any_one(rest, path))

# a divide's divisor, when the call is a divide
def on_div_is(+div: Bool, +as: List<&2, Tree.Node>, +path: String) -> List<&2, F.Finding>:
  match div:
    case True{}:
      cite(last_one(as), path)
    case False{}:
      Nil{}

# a divide's divisor, when the call is a divide
def on_div(+tt: String, +as: List<&2, Tree.Node>, +path: String) -> List<&2, F.Finding>:
  on_div_is(List.contains(~String, ~String.eq, ["Nat.div", "U32.div", "F32.div"], tt), as, path)

# a multiply (either factor) or a divide (the divisor only)
def on_op_is(+mul: Bool, +tt: String, +as: List<&2, Tree.Node>, +path: String) -> List<&2, F.Finding>:
  match mul:
    case True{}:
      any_one(as, path)
    case False{}:
      on_div(tt, as, path)

# a multiply (either factor) or a divide (the divisor only)
def on_op(+tt: String, +as: List<&2, Tree.Node>, +path: String) -> List<&2, F.Finding>:
  on_op_is(List.contains(~String, ~String.eq, ["Nat.mul", "U32.mul", "F32.mul"], tt), tt, as, path)

# the call's own identity operands, when this step recurses
def on_hot(hot: Bool, +tt: String, +as: List<&2, Tree.Node>, +path: String) -> List<&2, F.Finding>:
  match hot:
    case False{}:
      Nil{}
    case True{}:
      on_op(tt, as, path)

# the call's own identity operands, when this step recurses
def on_call(+tt: String, kids: Tree.Node, +path: String, +hot: Bool) -> List<&2, F.Finding>:
  on_hot(hot, tt, Calls.args(kids), path)

# the call's findings when the group is an application
def own_of(
  call: Bool,
  +tt: String,
  +kids: Tree.Node,
  +path: String,
  +hot: Bool
) -> List<&2, F.Finding>:
  match call:
    case True{}:
      on_call(tt, kids, path, hot)
    case False{}:
      Nil{}

# the first leaf, when the chain starts with one
def first_tok(nn: Tree.Node) -> Maybe<&2, Lex.Tok>:
  match nn:
    case Tree.NCons{Tree.Leaf{tok}, rest}:
      Some{tok}
    case other:
      None{}

# `*` / `/` by one, and the same through calls, in a hot region
def walk(nn: Tree.Node, +prev: Maybe<&2, Lex.Tok>, +self: String, +path: String, +hot: Bool) -> List<&2, F.Finding>:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TLam{}, t, l, c}}, +rest}:
      walk(rest, None{}, self, path, False{})
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, +t, +l, +c}}, Tree.NCons{Tree.Group{Lex.Tok{_, +o, _, _}, +kids, _}, rest}}:
      +call = String.eq(o, "(")
      +own = own_of(call, t, kids, path, hot)
      +inner = walk(kids, None{}, self, path, hot)
      +after = walk(rest, None{}, self, path, hot)
      List.concat(&2, F.Finding, [inner, own, after])
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TOp{}, +t, l, c}}, +rest}:
      +nxt = first_tok(rest)
      +hit = Bool.and(hot, identity(t, prev, nxt))
      +more = walk(rest, None{}, self, path, hot)
      List.append(&2, F.Finding, Bool.pick(List<&2, F.Finding>, hit, cite(which(t, prev, nxt), path), []), more)
    case Tree.NCons{Tree.Leaf{tok}, +rest}:
      walk(rest, Some{tok}, self, path, hot)
    case Tree.NCons{Tree.Group{open, +kids, close}, rest}:
      List.concat(&2, F.Finding, [walk(kids, None{}, self, path, hot), walk(rest, None{}, self, path, hot)])
    case Tree.NCons{Tree.Stmt{Tree.SCase{}, kids, +body}, rest}:
      +arm = Bool.and(hot, Calls.calls(body, self))
      List.concat(&2, F.Finding, [walk(kids, None{}, self, path, False{}),
        walk(body, None{}, self, path, arm), walk(rest, None{}, self, path, hot)])
    case Tree.NCons{Tree.Stmt{kind, kids, body}, rest}:
      List.concat(&2, F.Finding, [walk(kids, None{}, self, path, hot),
        walk(body, None{}, self, path, hot), walk(rest, None{}, self, path, hot)])
    case Tree.NCons{h, rest}:
      walk(rest, prev, self, path, hot)
    case other:
      Nil{}

def check.go(ds: List<&2, Calls.Def>, +path: String, acc: List<&2, List<&2, F.Finding>>) -> List<&2, F.Finding>:
  match ds:
    case Nil{}:
      List.concat(&2, F.Finding, List.reverse(&2, List<&2, F.Finding>, acc))
    case Con{Calls.Def{+name, +sig, +body}, rest}:
      check.go(rest, path,
        Lazy.stop(List<&2, F.Finding>,
          Bool.not(Bool.and(Calls.calls(body, name), Bool.not(Calls.exempt(path, sig)))), [],
          _u => walk(body, None{}, name, path, True{})) <> acc)

# the rule
def check(ss: Src.Src) -> List<&2, F.Finding>:
  Src.Src{path, text, toks, tree, bound, items} = ss
  check.go(Calls.defs(tree), path, [])
