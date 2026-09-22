# rule ring: a self-call argument that both drops a fixed count off a named
# window and appends onto that result (`List.drop` / `List.tail` /
# `String.drop` / `String.tail`, then `List.append` / `String.append` / `++`).
# Each step copies the window. Keep it in an Array and advance an index.
# Growing an accumulator by append, with no drop of that same value, is
# `concat`. Laws and proofs do not run.
import Base
import ../../src.bend as Src
import ../../finding.bend as F
import ../../../syntax/lex.bend as Lex
import ../../../syntax/tree.bend as Tree
import ../calls.bend as Calls
import ../../../lazy/lazy.bend as Lazy

# the first of two maybes
def or_tok(aa: Maybe<&2, Lex.Tok>, +bb: Maybe<&2, Lex.Tok>) -> Maybe<&2, Lex.Tok>:
  match aa:
    case Some{+t}:
      Some{t}
    case None{}:
      bb

# is the chain exactly one lowercase name?
def is_name(nn: Tree.Node) -> Bool:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, t, l, c}}, Tree.NNil{}}:
      True{}
    case other:
      False{}

# is the chain exactly one number?
def is_num(nn: Tree.Node) -> Bool:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TNum{}, t, l, c}}, Tree.NNil{}}:
      True{}
    case other:
      False{}

# does any argument name the window?
def has_name(as: List<&2, Tree.Node>) -> Bool:
  match as:
    case Nil{}:
      False{}
    case Con{h, rest}:
      +more = has_name(rest)
      Bool.or(is_name(h), more)

# is the last argument a number?
def last_num(as: List<&2, Tree.Node>) -> Bool:
  match as:
    case Nil{}:
      False{}
    case Con{h, Nil{}}:
      is_num(h)
    case Con{h, rest}:
      last_num(rest)

# a fixed drop or tail of a named window
def drop_ok(+tt: String, +as: List<&2, Tree.Node>) -> Bool:
  +kind = List.contains(~String, ~String.eq, ["List.drop", "String.drop", "List.tail", "String.tail"], tt)
  +tail = Bool.or(String.eq(tt, "List.tail"), String.eq(tt, "String.tail"))
  Bool.and(kind, Bool.and(has_name(as), Bool.or(tail, last_num(as))))

# the callee token when this call is a fixed drop
def drop_tok(kk: Lex.TokKind, +tt: String, +line: U32, +col: U32, kids: Tree.Node) -> Maybe<&2, Lex.Tok>:
  Bool.pick(Maybe<&2, Lex.Tok>, drop_ok(tt, Calls.args(kids)), Some{Lex.Tok{kk, tt, line, col}}, None{})

# the drop this call is, when the group is an application
def here_of(
  +open: Bool,
  kk: Lex.TokKind,
  +tt: String,
  +line: U32,
  +col: U32,
  kids: Tree.Node
) -> Maybe<&2, Lex.Tok>:
  match open:
    case False{}:
      None{}
    case True{}:
      drop_tok(kk, tt, line, col, kids)

# a drop anywhere under the node
def drop_in(nn: Tree.Node) -> Maybe<&2, Lex.Tok>:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{+k, +t, +l, +c}}, Tree.NCons{Tree.Group{Lex.Tok{_, +o, _, _}, +kids, _}, rest}}:
      +here = here_of(String.eq(o, "("), k, t, l, c, kids)
      +inn = drop_in(kids)
      +aft = drop_in(rest)
      or_tok(here, or_tok(inn, aft))
    case Tree.NCons{Tree.Group{open, kids, close}, rest}:
      or_tok(drop_in(kids), drop_in(rest))
    case Tree.NCons{Tree.Stmt{kind, kids, body}, rest}:
      or_tok(drop_in(kids), or_tok(drop_in(body), drop_in(rest)))
    case Tree.NCons{h, rest}:
      drop_in(rest)
    case other:
      None{}

# which list an append extends
def receiver_is(+list: Bool, +str: Bool, +as: List<&2, Tree.Node>) -> Maybe<&2, Lex.Tok>:
  match list str:
    case True{} b:
      drop_in(Calls.arg(as, 2n))
    case False{} True{}:
      drop_in(Calls.arg(as, 0n))
    case False{} False{}:
      None{}

# the drop an append copies onto, when this call is List.append or String.append
def receiver(+tt: String, kids: Tree.Node) -> Maybe<&2, Lex.Tok>:
  receiver_is(String.eq(tt, "List.append"), String.eq(tt, "String.append"), Calls.args(kids))

# a `++` whose left already dropped: that drop; otherwise nothing
def pp_found(+is_pp: Bool, seen: Maybe<&2, Lex.Tok>) -> Maybe<&2, Lex.Tok>:
  match is_pp seen:
    case True{} Some{+t}:
      Some{t}
    case True{} None{}:
      None{}
    case False{} s:
      None{}

# the drop still in play after this operator (`++` starts a new left side)
def pp_seen(+is_pp: Bool, +seen: Maybe<&2, Lex.Tok>) -> Maybe<&2, Lex.Tok>:
  match is_pp:
    case True{}:
      None{}
    case False{}:
      seen

# an application's append-receiver drop; a bracket is not an application
def call_recv(+open: Bool, +tt: String, kids: Tree.Node) -> Maybe<&2, Lex.Tok>:
  match open:
    case False{}:
      None{}
    case True{}:
      receiver(tt, kids)

# a drop this node itself is: the call when it is an application, else under a bracket
def call_drop(
  +open: Bool,
  +kk: Lex.TokKind,
  +tt: String,
  +line: U32,
  +col: U32,
  +kids: Tree.Node
) -> Maybe<&2, Lex.Tok>:
  match open:
    case False{}:
      drop_in(kids)
    case True{}:
      drop_tok(kk, tt, line, col, kids)

# a drop then `++`, or an append onto a drop, in this chain
def plus_scan(nn: Tree.Node, +seen: Maybe<&2, Lex.Tok>) -> Maybe<&2, Lex.Tok>:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TOp{}, +op, l, c}}, rest}:
      +is_pp = String.eq(op, "++")
      or_tok(pp_found(is_pp, seen), plus_scan(rest, pp_seen(is_pp, seen)))
    case Tree.NCons{Tree.Leaf{Lex.Tok{+k, +t, +l, +c}}, Tree.NCons{Tree.Group{Lex.Tok{_, +o, _, _}, +kids, _}, rest}}:
      +open = String.eq(o, "(")
      +recv = call_recv(open, t, kids)
      +inn = plus_scan(kids, None{})
      +drop = call_drop(open, k, t, l, c, kids)
      +aft = plus_scan(rest, or_tok(seen, drop))
      or_tok(recv, or_tok(inn, aft))
    case Tree.NCons{Tree.Group{open, +kids, close}, rest}:
      +inn = plus_scan(kids, None{})
      +aft = plus_scan(rest, or_tok(seen, drop_in(kids)))
      or_tok(inn, aft)
    case Tree.NCons{Tree.Stmt{kind, kids, body}, rest}:
      or_tok(plus_scan(kids, None{}), or_tok(plus_scan(body, None{}), plus_scan(rest, seen)))
    case Tree.NCons{h, rest}:
      plus_scan(rest, seen)
    case other:
      None{}

# a finding at the drop the scan found
def slide_at(mm: Maybe<&2, Lex.Tok>, +path: String) -> List<&2, F.Finding>:
  match mm:
    case None{}:
      Nil{}
    case Some{Lex.Tok{k, +t, l, c}}:
      [F.Finding{path, l, c, U32.from_nat(String.length(t)), "ring",
        "This step drops and appends a fixed window, which copies it; keep the window in an Array and advance an index."}]

# a finding at the drop, when the argument slides a window
def slide(aa: Tree.Node, +path: String) -> List<&2, F.Finding>:
  slide_at(plus_scan(aa, None{}), path)

# every self-call argument that slides
def slides(as: List<&2, Tree.Node>, +path: String) -> List<&2, F.Finding>:
  match as:
    case Nil{}:
      Nil{}
    case Con{h, rest}:
      List.append(&2, F.Finding, slide(h, path), slides(rest, path))

# every self-call's sliding arguments
def walk(nn: Tree.Node, +self: String, +path: String) -> List<&2, F.Finding>:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, +t, l, c}}, Tree.NCons{Tree.Group{Lex.Tok{_, +o, _, _}, +kids, _}, rest}}:
      +me = Bool.and(String.eq(o, "("), String.eq(t, self))
      +own = Lazy.stop(List<&2, F.Finding>, Bool.not(me), [], _u => slides(Calls.args(kids), path))
      List.concat(&2, F.Finding, [own, walk(kids, self, path), walk(rest, self, path)])
    case Tree.NCons{Tree.Group{open, kids, close}, rest}:
      List.concat(&2, F.Finding, [walk(kids, self, path), walk(rest, self, path)])
    case Tree.NCons{Tree.Stmt{kind, kids, body}, rest}:
      List.concat(&2, F.Finding, [walk(kids, self, path), walk(body, self, path), walk(rest, self, path)])
    case Tree.NCons{h, rest}:
      walk(rest, self, path)
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
          _u => walk(body, name, path)) <> acc)

# the rule
def check(ss: Src.Src) -> List<&2, F.Finding>:
  Src.Src{path, text, toks, tree, bound, items} = ss
  check.go(Calls.defs(tree), path, [])
