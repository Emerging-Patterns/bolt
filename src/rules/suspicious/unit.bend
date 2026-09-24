# rule unit: a multiply or divide by the literal one (`1`, `1n`, `1.0`) on a
# step that actually recurses. `*` and `/` inside `(e : T)` are `T.mul` and
# `T.div`; bare, they are `Nat`. Either form, and a direct `Nat.mul` /
# `U32.mul` / `F32.mul` or `.div`, does nothing when an operand is one
# (`/` only when the divisor is). Drop the operation. Any other factor or
# divisor is left alone, and so is a base case or a def that does not call
# itself. A base case is a case arm that does not call the def; the arms are
# judged per `case` only, so a `Bool.pick` branch beside a self-call is still
# the recursive step, and so is a lambda body inside it (a `Lazy.stop`
# thunk or a `List.map` callback runs on the step). One finding per
# operation, on the literal: `Nat.mul(1n, 1n)` is one. Laws and proofs do not
# run (a def with no type at all fills a law: it is a proof).
import Base
import ../../src.bend as Src
import ../../finding.bend as F
import ../../syntax/lex.bend as Lex
import ../../syntax/tree.bend as Tree
import ../calls.bend as Calls
import ../../lazy/lazy.bend as Lazy

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

# is the kind an operator's?
def op_kind(kk: Lex.TokKind) -> Bool:
  match kk:
    case Lex.TOp{}:
      True{}
    case other:
      False{}

# the maybe, when it holds the literal one
def one_of(mm: Maybe<&2, Lex.Tok>) -> Maybe<&2, Lex.Tok>:
  match mm:
    case None{}:
      None{}
    case Some{+tok}:
      Bool.pick(Maybe<&2, Lex.Tok>, one_tok(tok), Some{tok}, None{})

# the first maybe when it holds a token, else the second
def either(aa: Maybe<&2, Lex.Tok>, bb: Maybe<&2, Lex.Tok>) -> Maybe<&2, Lex.Tok>:
  match aa:
    case None{}:
      bb
    case Some{tok}:
      Some{tok}

# the literal an operator's finding points at: for `*` the factor after it
# when it is one, else the one before; for `/` the divisor when it is one
def which(+op: String, prev: Maybe<&2, Lex.Tok>, +nxt: Maybe<&2, Lex.Tok>) -> Maybe<&2, Lex.Tok>:
  +right = one_of(nxt)
  Bool.pick(Maybe<&2, Lex.Tok>, String.eq(op, "*"), either(right, one_of(prev)),
    Bool.pick(Maybe<&2, Lex.Tok>, String.eq(op, "/"), right, None{}))

# a finding on that literal
def cite(mm: Maybe<&2, Lex.Tok>, +path: String) -> List<&2, F.Finding>:
  match mm:
    case None{}:
      Nil{}
    case Some{Lex.Tok{k, +t, l, c}}:
      [F.Finding{path, l, c, U32.from_nat(String.length(t)), "unit",
        "Multiplying or dividing by " ++ t ++ " has no effect; drop the operation."}]

# an argument that is exactly the literal one
def arg_one(aa: Tree.Node) -> Maybe<&2, Lex.Tok>:
  match aa:
    case Tree.NCons{Tree.Leaf{tok}, Tree.NNil{}}:
      one_of(Some{tok})
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

# the last argument that is the literal one
def any_one(as: List<&2, Tree.Node>) -> Maybe<&2, Lex.Tok>:
  match as:
    case Nil{}:
      None{}
    case Con{h, rest}:
      +more = any_one(rest)
      either(more, arg_one(h))

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
      cite(any_one(as), path)
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

# the token a leaf leaves behind for what follows it: none past an operator
def after(tok: Lex.Tok) -> Maybe<&2, Lex.Tok>:
  match tok:
    case Lex.Tok{+k, +t, +l, +c}:
      Bool.pick(Maybe<&2, Lex.Tok>, op_kind(k), None{}, Some{Lex.Tok{k, t, l, c}})

# a leaf's own finding: an operator by one, in a hot region
def op_hit(
  tok: Lex.Tok,
  +prev: Maybe<&2, Lex.Tok>,
  +nxt: Maybe<&2, Lex.Tok>,
  +path: String,
  +hot: Bool
) -> List<&2, F.Finding>:
  match tok:
    case Lex.Tok{k, +t, l, c}:
      Bool.pick(List<&2, F.Finding>, Bool.and(hot, op_kind(k)), cite(which(t, prev, nxt), path), [])

# the name a group is called by: the token right before it ("" for none)
def callee(mm: Maybe<&2, Lex.Tok>) -> String:
  match mm:
    case None{}:
      ""
    case Some{Lex.Tok{k, t, l, c}}:
      t

# `*` / `/` by one, and the same through calls, in a hot region. prev is the
# leaf right before, none past an operator, a group or a statement; a `(`
# group right after a leaf is a call of it
def walk(nn: Tree.Node, +prev: Maybe<&2, Lex.Tok>, +self: String, +path: String, +hot: Bool) -> List<&2, F.Finding>:
  match nn:
    case Tree.NCons{Tree.Leaf{+tok}, +rest}:
      +more = walk(rest, after(tok), self, path, hot)
      List.append(&2, F.Finding, op_hit(tok, prev, first_tok(rest), path, hot), more)
    case Tree.NCons{Tree.Group{Lex.Tok{_, +o, _, _}, +kids, _}, rest}:
      +own = own_of(String.eq(o, "("), callee(prev), kids, path, hot)
      +inner = walk(kids, None{}, self, path, hot)
      +later = walk(rest, None{}, self, path, hot)
      List.concat(&2, F.Finding, [inner, own, later])
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
