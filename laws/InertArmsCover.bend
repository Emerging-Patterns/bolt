# What a comment or a string literal says changes nothing arms' cover check
# finds (laws/ArmsReportCoveredArms.bend): two sources whose trees read the
# same with comments and strings cut have the same findings. No hypothesis
# on how the lexer made the tokens is needed: the check reads the tree with
# every string's text left out (Arms.blank).
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/syntax/bind.bend as Bind
import ../src/src.bend as Src
import ../src/syntax/tree.bend as Tree
import ../src/syntax/outline.bend as Outline
import ../src/rules/correctness/arms.bend as Arms
import ./defs/InertText.bend as D1

# LAW: arms' cover check reads what no comment or string says: two sources
# whose trees read the same with comments and strings cut have the same
# findings
law inert_arms_cover:
  for +path: String
  for text: String
  for +tree: Tree.Node
  for toks: List<&2, Lex.Tok>
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  for text2: String
  for +tree2: Tree.Node
  for toks2: List<&2, Lex.Tok>
  for bound2: Bind.Bound
  for items2: List<&2, Outline.Item>
  for e: {D1.inert.node(tree) == D1.inert.node(tree2) : Tree.Node}
  {Arms.cover(Src.Src{path, text, toks, tree, bound, items})
    == Arms.cover(Src.Src{path, text2, toks2, tree2, bound2, items2}) : List<&2, F.Finding>}
