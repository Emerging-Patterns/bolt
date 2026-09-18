# syntax/tree: a source as a concrete syntax tree over its significant tokens:
# statements by line and indentation, groups by brackets. Built by one stack
# machine over the token list, so a half-written file still yields a tree:
#   - a bracket that never closes is closed by the next line at column 0
#     (so damage stays inside one item), or by the end of the file;
#   - a close bracket that matches nothing on the stack is a stray leaf;
#   - `<` opens type arguments only when glued to a name (`List<`, `Maybe<&`);
#     a `>`-only operator closes as many angle groups as it has `>`s.
# Trivia (spaces, newlines, comments) is not in the tree: read the tokens for
# that. The cells (NNil, NCons) live inside the type, as json/value does, so
# every walk is a structural recursion on one argument.
import Base
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

# a chain as a list
def to_list(cells: Node) -> List<&2, Node>:
  match cells:
    case NCons{h, t}:
      h <> to_list(t)
    case other:
      Nil{}

# a list as a chain
def of_list(ns: List<&2, Node>) -> Node:
  match ns:
    case Nil{}:
      NNil{}
    case Con{h, t}:
      NCons{h, of_list(t)}

# the token a leaf holds; a group's open, a statement's first token
def first(n: Node) -> Maybe<&2, Lex.Tok>:
  match n:
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

def text.of(m: Maybe<&2, Lex.Tok>) -> String:
  match m:
    case None{}:
      ""
    case Some{Lex.Tok{k, t, l, c}}:
      t

# the text of a node's first token ("" for none)
def text(n: Node) -> String:
  text.of(first(n))

def line.of(m: Maybe<&2, Lex.Tok>) -> U32:
  match m:
    case None{}:
      0
    case Some{Lex.Tok{k, t, l, c}}:
      l

# the line of a node's first token (0 for none)
def line(n: Node) -> U32:
  line.of(first(n))

def col.of(m: Maybe<&2, Lex.Tok>) -> U32:
  match m:
    case None{}:
      0
    case Some{Lex.Tok{k, t, l, c}}:
      c

# the column of a node's first token (0 for none)
def col(n: Node) -> U32:
  col.of(first(n))

# is it a single token?
def is_leaf(n: Node) -> Bool:
  match n:
    case Leaf{tok}:
      True{}
    case other:
      False{}

# is it the leaf with this text?
def is_text(n: Node, +s: String) -> Bool:
  match n:
    case Leaf{Lex.Tok{k, t, l, c}}:
      String.eq(t, s)
    case other:
      False{}

# is it a group opened by this bracket?
def opens(n: Node, +s: String) -> Bool:
  match n:
    case Group{Lex.Tok{k, t, l, c}, kids, close}:
      String.eq(t, s)
    case other:
      False{}

# the leaves of a tree, in order: the significant tokens
def leaf_close(close: Maybe<&2, Lex.Tok>, acc: List<&2, Lex.Tok>) -> List<&2, Lex.Tok>:
  match close:
    case None{}:
      acc
    case Some{tok}:
      tok <> acc

def leaves.go(n: Node, acc: List<&2, Lex.Tok>) -> List<&2, Lex.Tok>:
  match n:
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
def leaves(n: Node) -> List<&2, Lex.Tok>:
  List.reverse(&2, Lex.Tok, leaves.go(n, []))

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
def closer(+o: String) -> String:
  Bool.pick(String, String.eq(o, "("), ")",
    Bool.pick(String, String.eq(o, "["), "]",
      Bool.pick(String, String.eq(o, "{"), "}", ">")))

# is every char a `>`?
def all_gt(cs: List<&2, Char>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{+c, t}:
      Bool.and(Char.is_eq(c, '>'), all_gt(t))

# a token that closes a group: `)`, `]`, `}` or a run of `>`
def closes_with(k: Lex.TokKind, +t: String) -> Bool:
  match k:
    case Lex.TClose{}:
      True{}
    case Lex.TOp{}:
      Bool.and(Bool.not(String.is_empty(t)), all_gt(String.to_list(t)))
    case other:
      False{}

# `<` or `<&` right after a name opens type arguments
def opens_angle(k: Lex.TokKind, +t: String, glued: Bool) -> Bool:
  match k:
    case Lex.TOp{}:
      Bool.and(glued, Bool.or(String.eq(t, "<"), String.eq(t, "<&")))
    case other:
      False{}

# a finished node lands in the frame below
def put(stack: List<&2, Frame>, n: Node) -> List<&2, Frame>:
  match stack:
    case Nil{}:
      Nil{}
    case Con{FGroup{open, kids}, rest}:
      FGroup{open, NCons{n, kids}} <> rest
    case Con{FStmt{indent, kids, body}, rest}:
      FStmt{indent, NCons{n, kids}, body} <> rest
    case Con{FRoot{body}, rest}:
      FRoot{NCons{n, body}} <> rest

# the innermost open group, closed by close (None: never closed)
def close_one(stack: List<&2, Frame>, close: Maybe<&2, Lex.Tok>) -> List<&2, Frame>:
  match stack:
    case Con{FGroup{open, kids}, rest}:
      put(rest, Group{open, reverse(kids, NNil{}), close})
    case other:
      other

# how many groups sit open above the one that c closes (counting it); 0 when
# none does
def depth_to(stack: List<&2, Frame>, +c: String) -> Nat:
  match stack:
    case Nil{}:
      0n
    case Con{FGroup{Lex.Tok{k, +t, l, c2}, kids}, rest}:
      +below = depth_to(rest, c)
      Bool.pick(Nat, String.eq(closer(t), c), 1n,
        Bool.pick(Nat, Nat.is_eq(below, 0n), 0n, Succ{below}))
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
def close_n(n: Nat, stack: List<&2, Frame>, close: Maybe<&2, Lex.Tok>) -> List<&2, Frame>:
  match n:
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
  Bool.pick(List<&2, Frame>, Nat.is_eq(n, 0n), put(stack, Leaf{close}), close_n(n, stack, Some{close}))

# `>>` closes two angle groups
def close_gts(cs: List<&2, Char>, stack: List<&2, Frame>, +l: U32, +c: U32) -> List<&2, Frame>:
  match cs:
    case Nil{}:
      stack
    case Con{ch, t}:
      close_gts(t, close_tok(stack, Lex.Tok{Lex.TOp{}, ">", l, c}), l, (c + 1 : U32))

# a close bracket, or a run of `>`, closes what it can
def close_any(+stack: List<&2, Frame>, +close: Lex.Tok) -> List<&2, Frame>:
  Lex.Tok{k, +t, +l, +c} = close
  Bool.pick(List<&2, Frame>, String.starts_with(t, ">"),
    close_gts(String.to_list(t), stack, l, c), close_tok(stack, close))

# a finished statement lands in the body of the frame below
def put_stmt(stack: List<&2, Frame>, n: Node) -> List<&2, Frame>:
  match stack:
    case Con{FStmt{indent, kids, body}, rest}:
      FStmt{indent, kids, NCons{n, body}} <> rest
    case Con{FRoot{body}, rest}:
      FRoot{NCons{n, body}} <> rest
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
def keyword_kind(+t: String) -> StmtKind:
  Bool.pick(StmtKind, String.eq(t, "def"), SDef{},
    Bool.pick(StmtKind, String.eq(t, "type"), SType{},
      Bool.pick(StmtKind, String.eq(t, "law"), SLaw{},
        Bool.pick(StmtKind, String.eq(t, "import"), SImport{},
          Bool.pick(StmtKind, String.eq(t, "case"), SCase{},
            Bool.pick(StmtKind, Bool.or(String.eq(t, "for"), String.eq(t, "exs")), SFor{}, STerm{}))))))

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
def end_n(n: Nat, stack: List<&2, Frame>) -> List<&2, Frame>:
  match n:
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
def open_stmt(+stack: List<&2, Frame>, +c: U32) -> List<&2, Frame>:
  Bool.pick(List<&2, Frame>, in_group(stack), stack, FStmt{c, NNil{}, NNil{}} <> end_n(deeper(stack, c), stack))

# a significant token that starts a line: at column 0 it closes every open
# group (unless it is a bracket closing one of them); outside a group it opens
# a statement
def fresh(+stack: List<&2, Frame>, +tok: Lex.Tok) -> List<&2, Frame>:
  Lex.Tok{k, t, l, +c} = tok
  +cuts = Bool.and(Bool.and(in_group(stack), U32.is_eq(c, 0)), Nat.is_eq(depth_to(stack, t), 0n))
  open_stmt(Bool.pick(List<&2, Frame>, cuts, close_all(stack), stack), c)

# an open bracket or a leaf into the innermost frame
def push(+stack: List<&2, Frame>, +tok: Lex.Tok, glued: Bool) -> List<&2, Frame>:
  Lex.Tok{+k, +t, l, c} = tok
  Bool.pick(List<&2, Frame>, closes_with(k, t), close_any(stack, tok),
    Bool.pick(List<&2, Frame>, Bool.or(Lex.is_open(k), opens_angle(k, t, glued)), FGroup{tok, NNil{}} <> stack,
      put(stack, Leaf{tok})))

# glued: the previous token was a name with nothing between
def step(+tok: Lex.Tok, st: B, glued: Bool) -> B:
  Lex.Tok{+k, t, l, c} = tok
  B{+fr, +stack} = st
  Bool.pick(B, Lex.significant(k),
    B{False{}, push(Bool.pick(List<&2, Frame>, fr, fresh(stack, tok), stack), tok, glued)},
    B{Bool.or(fr, Lex.is_nl(k)), stack})

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
def show(n: Node) -> String:
  match n:
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
