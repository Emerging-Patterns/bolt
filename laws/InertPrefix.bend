# `prefix` reads no comment, space or newline: two sources whose significant
# tokens are the same have the same findings, whatever their comments say
# and wherever they are. A string literal's text it does read, since the
# literal's length decides a finding and the message quotes it, so prefix is
# among the rules laws/CodeRulesIgnoreCommentsAndStrings.bend leaves out; the
# shape written inside a string is one string token, never the shape
# (laws/PrefixReportsTakeComparedToLiteral.bend).
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/syntax/bind.bend as Bind
import ../src/src.bend as Src
import ../src/syntax/tree.bend as Tree
import ../src/syntax/outline.bend as Outline
import ../src/rules/suspicious/prefix.bend as Prefix
import ../src/rules/tokens.bend as T

# LAW: prefix reads no comment: two sources whose tokens are the same with
# spaces, newlines and comments dropped have the same findings
law inert_prefix:
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
  for e: {T.sig(toks) == T.sig(toks2) : List<&2, Lex.Tok>}
  {Prefix.check(Src.Src{path, text, toks, tree, bound, items})
    == Prefix.check(Src.Src{path, text2, toks2, tree2, bound2, items2}) : List<&2, F.Finding>}
