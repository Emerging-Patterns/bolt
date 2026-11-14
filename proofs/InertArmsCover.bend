# proofs of laws/InertArmsCover.bend
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/syntax/tree.bend as Tree
import ../src/rules/correctness/arms.bend as Arms
import ../laws/defs/InertText.bend as D1
import ../laws/InertArmsCover.bend as Laws

# a token read with its string or comment cut is blanked to the same token
law cover.tok:
  for tk: Lex.Tok
  {Arms.blank.tok(D1.inert.tok(tk)) == Arms.blank.tok(tk) : Lex.Tok}

def cover.tok(tk):
  match tk:
    case Lex.Tok{k, t, l, c}:
      match k:
        case Lex.TName{}:
          {==}
        case Lex.TUpper{}:
          {==}
        case Lex.TDotted{}:
          {==}
        case Lex.TWild{}:
          {==}
        case Lex.TKey{}:
          {==}
        case Lex.TNum{}:
          {==}
        case Lex.TStr{}:
          {==}
        case Lex.TChar{}:
          {==}
        case Lex.TComment{}:
          {==}
        case Lex.TSpace{}:
          {==}
        case Lex.TNewline{}:
          {==}
        case Lex.TOp{}:
          {==}
        case Lex.TColon{}:
          {==}
        case Lex.TEq{}:
          {==}
        case Lex.TBind{}:
          {==}
        case Lex.TArrow{}:
          {==}
        case Lex.TLam{}:
          {==}
        case Lex.TAll{}:
          {==}
        case Lex.TAmp{}:
          {==}
        case Lex.TOpen{}:
          {==}
        case Lex.TClose{}:
          {==}
        case Lex.TComma{}:
          {==}

# two nodes equal in each half are equal under a constructor of two
law cover.two:
  for -f: Tree.Node -> Tree.Node -> Tree.Node
  for -a: Tree.Node
  for -b: Tree.Node
  for -c: Tree.Node
  for -d: Tree.Node
  for e1: {a == b : Tree.Node}
  for e2: {c == d : Tree.Node}
  {f(a, c) == f(b, d) : Tree.Node}

def cover.two(f, a, b, c, d, e1, e2):
  Equal.trans(Tree.Node, f(a, c), f(b, c), f(b, d), Equal.cong(Tree.Node, Tree.Node, x => f(x, c), a, b, e1),
    Equal.cong(Tree.Node, Tree.Node, y => f(b, y), c, d, e2))

# a tree read with its strings and comments cut is blanked to the same tree
law cover.node:
  for n: Tree.Node
  {Arms.blank(D1.inert.node(n)) == Arms.blank(n) : Tree.Node}

def cover.node(n):
  match n:
    case Tree.Leaf{tok}:
      Equal.cong(Lex.Tok, Tree.Node, z => Tree.Leaf{z}, Arms.blank.tok(D1.inert.tok(tok)), Arms.blank.tok(tok),
        cover.tok(tok))
    case Tree.Group{open, kids, close}:
      Equal.cong(Tree.Node, Tree.Node, z => Tree.Group{open, z, close}, Arms.blank(D1.inert.node(kids)),
        Arms.blank(kids), cover.node(kids))
    case Tree.Stmt{kind, kids, body}:
      cover.two(x => y => Tree.Stmt{kind, x, y}, Arms.blank(D1.inert.node(kids)), Arms.blank(kids),
        Arms.blank(D1.inert.node(body)), Arms.blank(body), cover.node(kids), cover.node(body))
    case Tree.NNil{}:
      {==}
    case Tree.NCons{h, t}:
      cover.two(x => y => Tree.NCons{x, y}, Arms.blank(D1.inert.node(h)), Arms.blank(h),
        Arms.blank(D1.inert.node(t)), Arms.blank(t), cover.node(h), cover.node(t))

def Laws.inert_arms_cover(path, _text, tree, _toks, _bound, _items, _text2, tree2, _toks2, _bound2, _items2, e):
  Equal.trans(List<&2, F.Finding>, Arms.cover.walk(Arms.blank(tree), path),
    Arms.cover.walk(Arms.blank(D1.inert.node(tree)), path), Arms.cover.walk(Arms.blank(tree2), path),
    Equal.cong(Tree.Node, List<&2, F.Finding>, z => Arms.cover.walk(z, path), Arms.blank(tree),
      Arms.blank(D1.inert.node(tree)),
      Equal.sym(Tree.Node, Arms.blank(D1.inert.node(tree)), Arms.blank(tree), cover.node(tree))),
    Equal.trans(List<&2, F.Finding>, Arms.cover.walk(Arms.blank(D1.inert.node(tree)), path),
      Arms.cover.walk(Arms.blank(D1.inert.node(tree2)), path), Arms.cover.walk(Arms.blank(tree2), path),
      Equal.cong(Tree.Node, List<&2, F.Finding>, z => Arms.cover.walk(Arms.blank(z), path), D1.inert.node(tree),
        D1.inert.node(tree2), e),
      Equal.cong(Tree.Node, List<&2, F.Finding>, z => Arms.cover.walk(z, path), Arms.blank(D1.inert.node(tree2)),
        Arms.blank(tree2), cover.node(tree2))))
