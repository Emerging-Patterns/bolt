# part of: laws/CodeRulesIgnoreCommentsAndStrings.bend,
# laws/FromrevReportsReversedStringBuild.bend
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/syntax/bind.bend as Bind
import ../src/src.bend as Src
import ../src/syntax/tree.bend as Tree
import ../src/syntax/outline.bend as Outline
import ../src/rules/suspicious/fromrev.bend as Fromrev
import ./defs/InertText.bend as D1

# LAW: fromrev reads what no comment or string says: two sources as the
# lexer makes them whose tokens read the same with comments and strings cut
# have the same findings
law inert_fromrev:
  for +path: String
  for text: String
  for toks: List<&2, Lex.Tok>
  for tree: Tree.Node
  for bound: Bind.Bound
  for items: List<&2, Outline.Item>
  for text2: String
  for toks2: List<&2, Lex.Tok>
  for tree2: Tree.Node
  for bound2: Bind.Bound
  for items2: List<&2, Outline.Item>
  for ok: {D1.inert.oks(toks) == True{} : Bool}
  for ok2: {D1.inert.oks(toks2) == True{} : Bool}
  for e: {D1.inert.toks(toks) == D1.inert.toks(toks2) : List<&2, Lex.Tok>}
  {Fromrev.check(Src.Src{path, text, toks, tree, bound, items})
    == Fromrev.check(Src.Src{path, text2, toks2, tree2, bound2, items2}) : List<&2, F.Finding>}
