# src/src: one file, read once and parsed once. A rule is handed this, not
# the text: a tree parse of a 156 KB file costs 1.5 s here (the lexer alone
# 54 ms, and `Bind.bound` parses again), so twenty rules that each parsed
# the text made the linter twenty times slower than it needs to be.
import Base
import ./syntax/lex.bend as Lex
import ./syntax/tree.bend as Tree
import ./syntax/bind.bend as Bind
import ./syntax/outline.bend as Outline

# the path, the text, and the three readings of it every rule shares
type Src is Data:
  Src{path: String, text: String, toks: List<&2, Lex.Tok>, tree: Tree.Node, bound: Bind.Bound,
    items: List<&2, Outline.Item>}

# read a file's text once
def of(+path: String, +text: String) -> Src:
  +tree = Tree.parse(text)
  +toks = Lex.tokens(text)
  Src{path, text, toks, tree, Bind.of_tree(tree, String.lines(text)), Outline.of_tokens(text, toks)}
