# rule ring: a self-call replaces a binder with `List.append` of `List.drop`
# (or `String.append` / `++`, or `tail`) by a constant count, passing it back
# in the binder's own parameter position. Each step copies that fixed window.
# Keep it in an Array and advance an index. A list the def matches and walks
# (as any scrutinee of a match) is variable-length input, a window dropped
# into another parameter's slot is not carried, and a one-shot trim is not a
# loop: all stay quiet. Growing an accumulator by append, with no drop of
# that same value, is `concat`. Laws and proofs do not run.
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

# is the chain exactly one number?
def is_num(nn: Tree.Node) -> Bool:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TNum{}, t, l, c}}, Tree.NNil{}}:
      True{}
    case other:
      False{}

# the chain is exactly one lowercase name; its text, or empty
def name_text(nn: Tree.Node) -> String:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, +t, l, c}}, Tree.NNil{}}:
      t
    case other:
      ""

# this argument is a window binder
def win_name(nn: Tree.Node, +wins: List<&2, String>) -> Bool:
  +tt = name_text(nn)
  Bool.and(Bool.not(String.is_empty(tt)), List.contains(~String, ~String.eq, wins, tt))

# does any argument name the window?
def has_name(as: List<&2, Tree.Node>, +wins: List<&2, String>) -> Bool:
  match as:
    case Nil{}:
      False{}
    case Con{h, rest}:
      +more = has_name(rest, wins)
      Bool.or(win_name(h, wins), more)

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
def drop_ok(+tt: String, +as: List<&2, Tree.Node>, +wins: List<&2, String>) -> Bool:
  +kind = List.contains(~String, ~String.eq, ["List.drop", "String.drop", "List.tail", "String.tail"], tt)
  +tail = Bool.or(String.eq(tt, "List.tail"), String.eq(tt, "String.tail"))
  Bool.and(kind, Bool.and(has_name(as, wins), Bool.or(tail, last_num(as))))

# the callee token when this call is a fixed drop
def drop_tok(
  kk: Lex.TokKind,
  +tt: String,
  +line: U32,
  +col: U32,
  kids: Tree.Node,
  +wins: List<&2, String>
) -> Maybe<&2, Lex.Tok>:
  Bool.pick(Maybe<&2, Lex.Tok>, drop_ok(tt, Calls.args(kids), wins), Some{Lex.Tok{kk, tt, line, col}}, None{})

# the drop this call is, when the group is an application
def here_of(
  +open: Bool,
  kk: Lex.TokKind,
  +tt: String,
  +line: U32,
  +col: U32,
  kids: Tree.Node,
  +wins: List<&2, String>
) -> Maybe<&2, Lex.Tok>:
  match open:
    case False{}:
      None{}
    case True{}:
      drop_tok(kk, tt, line, col, kids, wins)

# a drop anywhere under the node
def drop_in(nn: Tree.Node, +wins: List<&2, String>) -> Maybe<&2, Lex.Tok>:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{+k, +t, +l, +c}}, Tree.NCons{Tree.Group{Lex.Tok{_, +o, _, _}, +kids, _}, rest}}:
      +here = here_of(String.eq(o, "("), k, t, l, c, kids, wins)
      +inn = drop_in(kids, wins)
      +aft = drop_in(rest, wins)
      or_tok(here, or_tok(inn, aft))
    case Tree.NCons{Tree.Group{open, +kids, close}, rest}:
      or_tok(drop_in(kids, wins), drop_in(rest, wins))
    case Tree.NCons{Tree.Stmt{kind, +kids, body}, rest}:
      or_tok(drop_in(kids, wins), or_tok(drop_in(body, wins), drop_in(rest, wins)))
    case Tree.NCons{h, rest}:
      drop_in(rest, wins)
    case other:
      None{}

# which list an append extends
def receiver_is(+list: Bool, +str: Bool, +as: List<&2, Tree.Node>, +wins: List<&2, String>) -> Maybe<&2, Lex.Tok>:
  match list str:
    case True{} b:
      drop_in(Calls.arg(as, 2n), wins)
    case False{} True{}:
      drop_in(Calls.arg(as, 0n), wins)
    case False{} False{}:
      None{}

# the drop an append copies onto, when this call is List.append or String.append
def receiver(+tt: String, kids: Tree.Node, +wins: List<&2, String>) -> Maybe<&2, Lex.Tok>:
  receiver_is(String.eq(tt, "List.append"), String.eq(tt, "String.append"), Calls.args(kids), wins)

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
def call_recv(+open: Bool, +tt: String, kids: Tree.Node, +wins: List<&2, String>) -> Maybe<&2, Lex.Tok>:
  match open:
    case False{}:
      None{}
    case True{}:
      receiver(tt, kids, wins)

# a drop this node itself is: the call when it is an application, else under a bracket
def call_drop(
  +open: Bool,
  +kk: Lex.TokKind,
  +tt: String,
  +line: U32,
  +col: U32,
  +kids: Tree.Node,
  +wins: List<&2, String>
) -> Maybe<&2, Lex.Tok>:
  match open:
    case False{}:
      drop_in(kids, wins)
    case True{}:
      drop_tok(kk, tt, line, col, kids, wins)

# a drop then `++`, or an append onto a drop, in this chain
def plus_scan(nn: Tree.Node, +seen: Maybe<&2, Lex.Tok>, +wins: List<&2, String>) -> Maybe<&2, Lex.Tok>:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TOp{}, +op, l, c}}, rest}:
      +is_pp = String.eq(op, "++")
      or_tok(pp_found(is_pp, seen), plus_scan(rest, pp_seen(is_pp, seen), wins))
    case Tree.NCons{Tree.Leaf{Lex.Tok{+k, +t, +l, +c}}, Tree.NCons{Tree.Group{Lex.Tok{_, +o, _, _}, +kids, _}, rest}}:
      +open = String.eq(o, "(")
      +recv = call_recv(open, t, kids, wins)
      +inn = plus_scan(kids, None{}, wins)
      +drop = call_drop(open, k, t, l, c, kids, wins)
      +aft = plus_scan(rest, or_tok(seen, drop), wins)
      or_tok(recv, or_tok(inn, aft))
    case Tree.NCons{Tree.Group{open, +kids, close}, rest}:
      +inn = plus_scan(kids, None{}, wins)
      +aft = plus_scan(rest, or_tok(seen, drop_in(kids, wins)), wins)
      or_tok(inn, aft)
    case Tree.NCons{Tree.Stmt{kind, +kids, body}, rest}:
      or_tok(plus_scan(kids, None{}, wins), or_tok(plus_scan(body, None{}, wins), plus_scan(rest, seen, wins)))
    case Tree.NCons{h, rest}:
      plus_scan(rest, seen, wins)
    case other:
      None{}

# a finding at the drop the scan found
def slide_at(mm: Maybe<&2, Lex.Tok>, +path: String) -> List<&2, F.Finding>:
  match mm:
    case None{}:
      Nil{}
    case Some{Lex.Tok{k, +t, l, c}}:
      [F.Finding{path, l, c, U32.from_nat(String.length(t)), "ring",
        "Each step drops from and appends to a fixed-size window, which copies it; keep the window in an Array and advance an index."}]

# a finding at the drop, when the argument slides a window
def slide(aa: Tree.Node, +path: String, +wins: List<&2, String>) -> List<&2, F.Finding>:
  slide_at(plus_scan(aa, None{}, wins), path)

# the windows an argument in this parameter's slot may slide: the parameter
# itself when it is a window, else none
def slot_wins(+slot: String, +wins: List<&2, String>) -> List<&2, String>:
  Bool.pick(List<&2, String>, List.contains(~String, ~String.eq, wins, slot), [slot], [])

# every self-call argument that slides the window of its own slot (params,
# from the argument's position on)
def slides(
  as: List<&2, Tree.Node>,
  +params: List<&2, String>,
  +path: String,
  +wins: List<&2, String>
) -> List<&2, F.Finding>:
  match as:
    case Nil{}:
      Nil{}
    case Con{h, rest}:
      +slot = Maybe.default(&2, String, List.head(&2, String, params), "")
      List.append(&2, F.Finding, slide(h, path, slot_wins(slot, wins)),
        slides(rest, List.tail(&2, String, params), path, wins))

# every self-call's sliding arguments
def walk(
  nn: Tree.Node,
  +self: String,
  +params: List<&2, String>,
  +path: String,
  +wins: List<&2, String>
) -> List<&2, F.Finding>:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{k, +t, l, c}}, Tree.NCons{Tree.Group{Lex.Tok{_, +o, _, _}, +kids, _}, rest}}:
      +me = Bool.and(String.eq(o, "("), String.eq(t, self))
      +own = Lazy.stop(List<&2, F.Finding>, Bool.not(me), [], _u => slides(Calls.args(kids), params, path, wins))
      List.concat(&2, F.Finding, [own, walk(kids, self, params, path, wins), walk(rest, self, params, path, wins)])
    case Tree.NCons{Tree.Group{open, +kids, close}, rest}:
      List.concat(&2, F.Finding, [walk(kids, self, params, path, wins), walk(rest, self, params, path, wins)])
    case Tree.NCons{Tree.Stmt{kind, +kids, body}, rest}:
      List.concat(&2, F.Finding, [walk(kids, self, params, path, wins), walk(body, self, params, path, wins),
        walk(rest, self, params, path, wins)])
    case Tree.NCons{h, rest}:
      walk(rest, self, params, path, wins)
    case other:
      Nil{}

# the top-level names of a chain, onto acc
def names_in(nn: Tree.Node, acc: List<&2, String>) -> List<&2, String>:
  match nn:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TName{}, t, l, c}}, rest}:
      t <> names_in(rest, acc)
    case Tree.NCons{h, rest}:
      names_in(rest, acc)
    case other:
      acc

# every scrutinee of `match a b ..:`, onto acc (acc alone for any other chain)
def match_names(kids: Tree.Node, +acc: List<&2, String>) -> List<&2, String>:
  match kids:
    case Tree.NCons{Tree.Leaf{Lex.Tok{Lex.TKey{}, +kw, l, c}}, +rest}:
      Lazy.stop(List<&2, String>, Bool.not(String.eq(kw, "match")), acc, _u => names_in(rest, acc))
    case other:
      acc

# names the def matches, as any scrutinee: variable-length input, not a window
def matched(nn: Tree.Node, +acc: List<&2, String>) -> List<&2, String>:
  match nn:
    case Tree.NCons{Tree.Stmt{Tree.STerm{}, +kids, body}, rest}:
      +here = match_names(kids, acc)
      matched(rest, matched(body, matched(kids, here)))
    case Tree.NCons{Tree.Stmt{kind, +kids, body}, rest}:
      matched(rest, matched(body, matched(kids, acc)))
    case Tree.NCons{Tree.Group{open, +kids, close}, rest}:
      matched(rest, matched(kids, acc))
    case Tree.NCons{h, rest}:
      matched(rest, acc)
    case other:
      acc

# parameters that are not matched as input
def windows.go(ps: List<&2, String>, +bad: List<&2, String>, +acc: List<&2, String>) -> List<&2, String>:
  match ps:
    case Nil{}:
      List.reverse(&2, String, acc)
    case Con{+p, rest}:
      +keep = Bool.and(Bool.not(String.is_empty(p)), Bool.not(List.contains(~String, ~String.eq, bad, p)))
      windows.go(rest, bad, Bool.pick(List<&2, String>, keep, p <> acc, acc))

# parameters that are not matched as input
def windows(sig: Tree.Node, body: Tree.Node) -> List<&2, String>:
  windows.go(Calls.names(sig), matched(body, []), [])

def check.go(ds: List<&2, Calls.Def>, +path: String, acc: List<&2, List<&2, F.Finding>>) -> List<&2, F.Finding>:
  match ds:
    case Nil{}:
      List.concat(&2, F.Finding, List.reverse(&2, List<&2, F.Finding>, acc))
    case Con{Calls.Def{+name, +sig, +body}, rest}:
      check.go(rest, path,
        Lazy.stop(List<&2, F.Finding>,
          Bool.not(Bool.and(Calls.calls(body, name), Bool.not(Calls.exempt(path, sig)))), [],
          _u => walk(body, name, Calls.names(sig), path, windows(sig, body))) <> acc)

# the rule
def check(ss: Src.Src) -> List<&2, F.Finding>:
  Src.Src{path, text, toks, tree, bound, items} = ss
  check.go(Calls.defs(tree), path, [])
