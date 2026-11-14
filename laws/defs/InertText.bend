# comments and strings read as inert text, cut and blanked
import Base
import ../../src/syntax/lex.bend as Lex
import ../../src/syntax/tree.bend as Tree

# Inert text (laws/CodeRulesIgnoreCommentsAndStrings.bend). A comment or a string literal says what it
# likes: changing what it says leaves every rule whose pattern is code with
# the same findings. A source is read here with each such token cut to its
# first char (`#` or `"`), everything else left as it is; two sources that
# read the same that way differ at most in what their comments and strings
# say, token for token, kinds and positions kept. The lexer starts a token
# with `"` or `#` exactly when it is a string or a comment (inert.ok): what
# a rule compares a string's text with, a name or a keyword, never starts
# that way.

# a comment or a string literal: a token whose text is not code
def inert.blanks(k: Lex.TokKind) -> Bool:
  match k:
    case Lex.TStr{}:
      True{}
    case Lex.TComment{}:
      True{}
    case other:
      False{}

# a text cut to its first char
def inert.cut(t: String) -> String:
  match t:
    case SNil{}:
      SNil{}
    case SCon{h, _t}:
      SCon{h, SNil{}}

# the text, cut when it is not code
def inert.keep(b: Bool, t: String) -> String:
  match b:
    case True{}:
      inert.cut(t)
    case False{}:
      t

# a token with what it says cut when it is a comment or a string
def inert.tok(tk: Lex.Tok) -> Lex.Tok:
  match tk:
    case Lex.Tok{+k, t, l, c}:
      Lex.Tok{k, inert.keep(inert.blanks(k), t), l, c}

# the tokens, each read that way
def inert.toks(ts: List<&2, Lex.Tok>) -> List<&2, Lex.Tok>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      inert.tok(h) <> inert.toks(t)

# a tree with each leaf read that way; brackets and statement kinds as they are
def inert.node(n: Tree.Node) -> Tree.Node:
  match n:
    case Tree.Leaf{tok}:
      Tree.Leaf{inert.tok(tok)}
    case Tree.Group{open, kids, close}:
      Tree.Group{open, inert.node(kids), close}
    case Tree.Stmt{kind, kids, body}:
      Tree.Stmt{kind, inert.node(kids), inert.node(body)}
    case Tree.NNil{}:
      Tree.NNil{}
    case Tree.NCons{h, t}:
      Tree.NCons{inert.node(h), inert.node(t)}

# `"` or `#`: the first char of a string or a comment
def inert.mark(c: Char) -> Bool:
  match c:
    case Chr{+x}:
      Bool.or(U32.is_eq(x, 34), U32.is_eq(x, 35))

# does the text start with `"` or `#`?
def inert.marked(t: String) -> Bool:
  match t:
    case SNil{}:
      False{}
    case SCon{h, _t}:
      inert.mark(h)

# a text starts with `"` or `#` exactly when b says it is not code
def inert.fits.go(b: Bool, t: String) -> Bool:
  match b:
    case True{}:
      inert.marked(t)
    case False{}:
      Bool.not(inert.marked(t))

# a token as the lexer makes it: marked exactly when it is a comment or a string
def inert.fits(tk: Lex.Tok) -> Bool:
  match tk:
    case Lex.Tok{+k, t, _l, _c}:
      inert.fits.go(inert.blanks(k), t)

# every token as the lexer makes it
def inert.oks(ts: List<&2, Lex.Tok>) -> Bool:
  match ts:
    case Nil{}:
      True{}
    case Con{h, t}:
      Bool.and(inert.fits(h), inert.oks(t))

# every leaf as the lexer makes it
def inert.ok(n: Tree.Node) -> Bool:
  match n:
    case Tree.Leaf{tok}:
      inert.fits(tok)
    case Tree.Group{_open, kids, _close}:
      inert.ok(kids)
    case Tree.Stmt{_kind, kids, body}:
      Bool.and(inert.ok(kids), inert.ok(body))
    case Tree.NNil{}:
      True{}
    case Tree.NCons{h, t}:
      Bool.and(inert.ok(h), inert.ok(t))
