# src/syntax/tree: a source as a concrete syntax tree over its significant tokens:
# statements by line and indentation, groups by brackets. Built by one stack
# machine over the token list, so a half-written file still yields a tree:
#   - a bracket that never closes is closed by the next line at column 0
#     (so damage stays inside one item), or by the end of the file;
#   - a close bracket that matches nothing on the stack is a stray leaf;
#   - `<` opens type arguments only when glued to a name (`List<`, `Maybe<&`);
#     a `>`-only operator closes as many angle groups as it has `>`s, each
#     only while an angle group is the innermost open one: in
#     `List<f(a > b)>` the first `>` is an operator inside `(..)`.
# Trivia (spaces, newlines, comments) is not in the tree: read the tokens for
# that. The cells (NNil, NCons) live inside the type, as json/value does, so
# every walk is a structural recursion on one argument.
import Base
import ../lazy/lazy.bend as Lazy
import ./lex.bend as Lex

# what a statement is, by its shape: SDef `def f(..)` (also `@unsafe def`),
# SType, SLaw, SImport, SCase `case p:`, SFor `for x: T` / `exs x: T`, SLet
# (a `=` or `<-` among its own tokens), else STerm (`match x:`, `do M<T>:`,
# `return e`, a call)
type StmtKind is Data:
  SDef{}
  SType{}
  SLaw{}
  SImport{}
  SCase{}
  SFor{}
  SLet{}
  STerm{}

# a leaf holds one token; a group its bracket, what is inside, and its close
# (None when it never closed); a statement its own tokens and the statements
# under it; NNil and NCons chain nodes
type Node is Data:
  Leaf{tok: Lex.Tok}
  Group{open: Lex.Tok, kids: Node, close: Maybe<&2, Lex.Tok>}
  Stmt{kind: StmtKind, kids: Node, body: Node}
  NNil{}
  NCons{head: Node, tail: Node}

# cells
# -----

# a chain, reversed onto acc
def reverse(cells: Node, acc: Node) -> Node:
  match cells:
    case NCons{h, t}:
      reverse(t, NCons{h, acc})
    case other:
      acc

# the token a leaf holds; a group's open, a statement's first token
def first(nn: Node) -> Maybe<&2, Lex.Tok>:
  match nn:
    case Leaf{tok}:
      Some{tok}
    case Group{open, kids, close}:
      Some{open}
    case Stmt{kind, kids, body}:
      first(kids)
    case NNil{}:
      None{}
    case NCons{h, t}:
      first(h)

def text.of(mm: Maybe<&2, Lex.Tok>) -> String:
  match mm:
    case None{}:
      ""
    case Some{Lex.Tok{k, t, l, c}}:
      t

# the text of a node's first token ("" for none)
def text(nn: Node) -> String:
  text.of(first(nn))

def line.of(mm: Maybe<&2, Lex.Tok>) -> U32:
  match mm:
    case None{}:
      0
    case Some{Lex.Tok{k, t, l, c}}:
      l

# the line of a node's first token (0 for none)
def line(nn: Node) -> U32:
  line.of(first(nn))

def col.of(mm: Maybe<&2, Lex.Tok>) -> U32:
  match mm:
    case None{}:
      0
    case Some{Lex.Tok{k, t, l, c}}:
      c

# the column of a node's first token (0 for none)
def col(nn: Node) -> U32:
  col.of(first(nn))

# is it a group opened by this bracket?
def opens(nn: Node, +ss: String) -> Bool:
  match nn:
    case Group{Lex.Tok{k, t, l, c}, kids, close}:
      String.eq(t, ss)
    case other:
      False{}

# the leaves of a tree, in order: the significant tokens
def leaf_close(close: Maybe<&2, Lex.Tok>, acc: List<&2, Lex.Tok>) -> List<&2, Lex.Tok>:
  match close:
    case None{}:
      acc
    case Some{tok}:
      tok <> acc

def leaves.go(nn: Node, acc: List<&2, Lex.Tok>) -> List<&2, Lex.Tok>:
  match nn:
    case Leaf{tok}:
      tok <> acc
    case Group{open, kids, close}:
      leaf_close(close, leaves.go(kids, open <> acc))
    case Stmt{kind, kids, body}:
      leaves.go(body, leaves.go(kids, acc))
    case NNil{}:
      acc
    case NCons{h, t}:
      leaves.go(t, leaves.go(h, acc))

# the leaves of a tree, in order: the significant tokens when the tree is faithful
def leaves(nn: Node) -> List<&2, Lex.Tok>:
  List.reverse(&2, Lex.Tok, leaves.go(nn, []))

# building
# --------

# an open group (its kids reversed), or an open statement (its kids and the
# finished statements under it, both reversed); the root holds the items
type Frame is Data:
  FGroup{open: Lex.Tok, kids: Node}
  FStmt{indent: U32, kids: Node, body: Node}
  FRoot{body: Node}

# fresh: the next significant token starts a line
type B is Data:
  B{fresh: Bool, stack: List<&2, Frame>}

# the bracket that closes an opener (`>` for `<` and `<&`)
def closer(+oo: String) -> String:
  Bool.pick(String, String.eq(oo, "("), ")",
    Bool.pick(String, String.eq(oo, "["), "]",
      Bool.pick(String, String.eq(oo, "{"), "}", ">")))

# is every char a `>`?
def all_gt(cs: List<&2, Char>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{+c, t}:
      Lazy.and_then(Char.is_eq(c, '>'), _u => all_gt(t))

# a token that closes a group: `)`, `]`, `}` or a run of `>`
def closes_with(kk: Lex.TokKind, +tt: String) -> Bool:
  match kk:
    case Lex.TClose{}:
      True{}
    case Lex.TOp{}:
      Bool.and(Bool.not(String.is_empty(tt)), all_gt(String.to_list(tt)))
    case other:
      False{}

# `<` or `<&` right after a name opens type arguments
def opens_angle(kk: Lex.TokKind, +tt: String, glued: Bool) -> Bool:
  match kk:
    case Lex.TOp{}:
      Bool.and(glued, Bool.or(String.eq(tt, "<"), String.eq(tt, "<&")))
    case other:
      False{}

# a finished node lands in the frame below
def put(stack: List<&2, Frame>, nn: Node) -> List<&2, Frame>:
  match stack:
    case Nil{}:
      Nil{}
    case Con{FGroup{open, kids}, rest}:
      FGroup{open, NCons{nn, kids}} <> rest
    case Con{FStmt{indent, kids, body}, rest}:
      FStmt{indent, NCons{nn, kids}, body} <> rest
    case Con{FRoot{body}, rest}:
      FRoot{NCons{nn, body}} <> rest

# the innermost open group, closed by close (None: never closed)
def close_one(stack: List<&2, Frame>, close: Maybe<&2, Lex.Tok>) -> List<&2, Frame>:
  match stack:
    case Con{FGroup{open, kids}, rest}:
      put(rest, Group{open, reverse(kids, NNil{}), close})
    case other:
      other

# one more group above the one found below, when one was
def depth_to.up(below: Nat) -> Nat:
  match below:
    case Zero{}:
      0n
    case Succ{p}:
      Succ{Succ{p}}

# how many groups sit open above the one that c closes (counting it); 0 when
# none does. A `>` closes only an angle group on top: inside `(..)`, `[..]`
# or `{..}` it is an operator, even within `<..>`
def depth_to(stack: List<&2, Frame>, +cc: String) -> Nat:
  match stack:
    case Nil{}:
      0n
    case Con{FGroup{Lex.Tok{k, +t, l, c2}, kids}, rest}:
      Lazy.stop(Nat, String.eq(closer(t), cc), 1n,
        _u => Lazy.stop(Nat, String.eq(cc, ">"), 0n, _v => depth_to.up(depth_to(rest, cc))))
    case Con{other, rest}:
      0n

# how many groups sit open on top of the stack
def groups(stack: List<&2, Frame>) -> Nat:
  match stack:
    case Con{FGroup{open, kids}, rest}:
      Succ{groups(rest)}
    case other:
      0n

# n groups close, innermost first; only the last gets the close token
def close_n(nn: Nat, stack: List<&2, Frame>, close: Maybe<&2, Lex.Tok>) -> List<&2, Frame>:
  match nn:
    case Zero{}:
      stack
    case Succ{Zero{}}:
      close_one(stack, close)
    case Succ{p}:
      close_n(p, close_one(stack, None{}), close)

# every open group closes, unclosed
def close_all(+stack: List<&2, Frame>) -> List<&2, Frame>:
  close_n(groups(stack), stack, None{})

# a close bracket: to its match if it has one, else a stray leaf
def close_tok(+stack: List<&2, Frame>, +close: Lex.Tok) -> List<&2, Frame>:
  Lex.Tok{k, +t, l, c} = close
  +n = depth_to(stack, t)
  Lazy.stop(List<&2, Frame>, Nat.is_eq(n, 0n), put(stack, Leaf{close}), _u => close_n(n, stack, Some{close}))

# `>>` closes two angle groups
def close_gts(cs: List<&2, Char>, stack: List<&2, Frame>, +ll: U32, +cc: U32) -> List<&2, Frame>:
  match cs:
    case Nil{}:
      stack
    case Con{ch, t}:
      close_gts(t, close_tok(stack, Lex.Tok{Lex.TOp{}, ">", ll, cc}), ll, (cc + 1 : U32))

# the close a bracket makes, given whether it is a run of `>`: a match, so
# only the side taken runs
def close_any.at(
  +gt: Bool,
  +stack: List<&2, Frame>,
  +close: Lex.Tok,
  +tt: String,
  +ll: U32,
  +cc: U32
) -> List<&2, Frame>:
  match gt:
    case True{}:
      close_gts(String.to_list(tt), stack, ll, cc)
    case False{}:
      close_tok(stack, close)

# a close bracket, or a run of `>`, closes what it can
def close_any(+stack: List<&2, Frame>, +close: Lex.Tok) -> List<&2, Frame>:
  Lex.Tok{k, +t, +l, +c} = close
  close_any.at(String.starts_with(t, ">"), stack, close, t, l, c)

# a finished statement lands in the body of the frame below
def put_stmt(stack: List<&2, Frame>, nn: Node) -> List<&2, Frame>:
  match stack:
    case Con{FStmt{indent, kids, body}, rest}:
      FStmt{indent, kids, NCons{nn, body}} <> rest
    case Con{FRoot{body}, rest}:
      FRoot{NCons{nn, body}} <> rest
    case other:
      other

# a `=` or `<-` among a statement's own tokens
def binds_in(kids: Node) -> Bool:
  match kids:
    case NCons{Leaf{Lex.Tok{Lex.TEq{}, t, l, c}}, rest}:
      True{}
    case NCons{Leaf{Lex.Tok{Lex.TBind{}, t, l, c}}, rest}:
      True{}
    case NCons{h, rest}:
      binds_in(rest)
    case other:
      False{}

# the kind of a statement led by this keyword
def keyword_kind(+tt: String) -> StmtKind:
  Bool.pick(StmtKind, String.eq(tt, "def"), SDef{},
    Bool.pick(StmtKind, String.eq(tt, "type"), SType{},
      Bool.pick(StmtKind, String.eq(tt, "law"), SLaw{},
        Bool.pick(StmtKind, String.eq(tt, "import"), SImport{},
          Bool.pick(StmtKind, String.eq(tt, "case"), SCase{},
            Bool.pick(StmtKind, Bool.or(String.eq(tt, "for"), String.eq(tt, "exs")), SFor{}, STerm{}))))))

# a statement's kind from its own tokens
def classify(kids: Node) -> StmtKind:
  match kids:
    case NCons{Leaf{Lex.Tok{Lex.TKey{}, t, l, c}}, rest}:
      keyword_kind(t)
    case NCons{Leaf{Lex.Tok{Lex.TAll{}, t, l, c}}, rest}:
      SDef{}
    case other:
      Bool.pick(StmtKind, binds_in(other), SLet{}, STerm{})

# the innermost open statement is finished and lands in its parent
def end_stmt(stack: List<&2, Frame>) -> List<&2, Frame>:
  match stack:
    case Con{FStmt{indent, kids, body}, rest}:
      +ks = reverse(kids, NNil{})
      put_stmt(rest, Stmt{classify(ks), ks, reverse(body, NNil{})})
    case other:
      other

# n statements finish, innermost first
def end_n(nn: Nat, stack: List<&2, Frame>) -> List<&2, Frame>:
  match nn:
    case Zero{}:
      stack
    case Succ{p}:
      end_n(p, end_stmt(stack))

# the statements a line at column col ends: those not shallower than it
def deeper(stack: List<&2, Frame>, +col: U32) -> Nat:
  match stack:
    case Con{FStmt{+indent, kids, body}, rest}:
      +below = deeper(rest, col)
      Bool.pick(Nat, U32.is_ge(indent, col), Succ{below}, 0n)
    case other:
      0n

# how many statements sit open on the stack
def stmts(stack: List<&2, Frame>) -> Nat:
  match stack:
    case Con{FStmt{indent, kids, body}, rest}:
      Succ{stmts(rest)}
    case other:
      0n

# is the innermost frame an open group?
def in_group(stack: List<&2, Frame>) -> Bool:
  match stack:
    case Con{FGroup{open, kids}, rest}:
      True{}
    case other:
      False{}

# a new statement at column c, once the ones it ends are finished; inside a
# group a line is just more tokens
def open_stmt(+stack: List<&2, Frame>, +cc: U32) -> List<&2, Frame>:
  Lazy.stop(List<&2, Frame>, in_group(stack), stack,
    _u => FStmt{cc, NNil{}, NNil{}} <> end_n(deeper(stack, cc), stack))

# a significant token that starts a line: at column 0 it closes every open
# group (unless it is a bracket closing one of them); outside a group it opens
# a statement
def fresh(+stack: List<&2, Frame>, +tok: Lex.Tok) -> List<&2, Frame>:
  Lex.Tok{k, t, l, +c} = tok
  +cuts = Bool.and(Bool.and(in_group(stack), U32.is_eq(c, 0)), Nat.is_eq(depth_to(stack, t), 0n))
  open_stmt(Lazy.stop(List<&2, Frame>, Bool.not(cuts), stack, _u => close_all(stack)), c)

# an open bracket or a leaf into the innermost frame
def push(+stack: List<&2, Frame>, +tok: Lex.Tok, glued: Bool) -> List<&2, Frame>:
  Lex.Tok{+k, +t, l, c} = tok
  Lazy.stop(List<&2, Frame>, Bool.not(closes_with(k, t)),
    Bool.pick(List<&2, Frame>, Bool.or(Lex.is_open(k), opens_angle(k, t, glued)), FGroup{tok, NNil{}} <> stack,
      put(stack, Leaf{tok})),
    _u => close_any(stack, tok))

# glued: the previous token was a name with nothing between
def step(+tok: Lex.Tok, st: B, glued: Bool) -> B:
  Lex.Tok{+k, t, l, c} = tok
  B{+fr, +stack} = st
  Lazy.stop(B, Bool.not(Lex.significant(k)), B{Bool.or(fr, Lex.is_nl(k)), stack},
    _u => B{False{}, push(Lazy.stop(List<&2, Frame>, Bool.not(fr), stack, _u2 => fresh(stack, tok)), tok, glued)})

# an identifier of any kind (what `<` glues to)
def is_name_tok(tok: Lex.Tok) -> Bool:
  Lex.Tok{k, t, l, c} = tok
  Lex.is_name(k)

# every token, in order
def run(toks: List<&2, Lex.Tok>, st: B, glued: Bool) -> B:
  match toks:
    case Nil{}:
      st
    case Con{+tok, t}:
      +g = is_name_tok(tok)
      run(t, step(tok, st, glued), g)

# the items gathered in the root frame
def root(stack: List<&2, Frame>) -> Node:
  match stack:
    case Con{FRoot{body}, rest}:
      reverse(body, NNil{})
    case other:
      NNil{}

# the tree once the tokens are over: every group and statement closes
def finish(st: B) -> Node:
  B{fr, stack} = st
  +closed = close_all(stack)
  root(end_n(stmts(closed), closed))

# the items of a source: a chain of statements
def of_tokens(toks: List<&2, Lex.Tok>) -> Node:
  finish(run(toks, B{True{}, [FRoot{NNil{}}]}, False{}))

# the items of a source: a chain of statements
def parse(source: String) -> Node:
  of_tokens(Lex.tokens(source))

# showing
# -------

# a group's close bracket, `..` when it never closed
def show_close(close: Maybe<&2, Lex.Tok>) -> String:
  match close:
    case None{}:
      ".."
    case Some{Lex.Tok{k, t, l, c}}:
      t

# `[def f (x : U32) -> U32 : {[match x {[case A {} : {[1]}]}]}]`: a statement
# in brackets, its body in braces, a group as its brackets (an unclosed one
# ends in `..`)
def show(nn: Node) -> String:
  match nn:
    case Leaf{Lex.Tok{k, t, l, c}}:
      t
    case Group{Lex.Tok{k, t, l, c}, kids, close}:
      t ++ show(kids) ++ show_close(close)
    case Stmt{kind, kids, body}:
      +b = show(body)
      "[" ++ show(kids) ++ Bool.pick(String, String.is_empty(b), "", " {" ++ b ++ "}") ++ "]"
    case NNil{}:
      ""
    case NCons{h, t}:
      +rest = show(t)
      show(h) ++ Bool.pick(String, String.is_empty(rest), "", " " ++ rest)
