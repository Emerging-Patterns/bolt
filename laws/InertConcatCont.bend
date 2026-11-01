# concat's continuation half (laws/ConcatReportsContinuationAppend.bend)
# reads code only, as its self-call half does
# (laws/CodeRulesIgnoreCommentsAndStrings.bend, inert_concat): changing the
# contents of a comment or string literal does not change its findings. It
# compares a leaf's text with the def's function-typed parameters, whose
# names no string equals, and an argument's appends only with names.
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/syntax/bind.bend as Bind
import ../src/src.bend as Src
import ../src/syntax/tree.bend as Tree
import ../src/syntax/outline.bend as Outline
import ../src/rules/suspicious/concat.bend as Concat
import ./defs/InertText.bend as D1

# LAW: concat's continuation half reads what no string says: two sources as
# the lexer makes them whose trees read the same with strings cut have the
# same findings
law inert_concat_cont:
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
  for +ok: {D1.inert.ok(tree) == True{} : Bool}
  for +ok2: {D1.inert.ok(tree2) == True{} : Bool}
  for e: {D1.inert.node(tree) == D1.inert.node(tree2) : Tree.Node}
  {Concat.cont(Src.Src{path, text, toks, tree, bound, items})
    == Concat.cont(Src.Src{path, text2, toks2, tree2, bound2, items2}) : List<&2, F.Finding>}
