# concat's continuation half (laws/ConcatReportsContinuationAppend.bend)
# follows the path exemption its self-call half does
# (laws/ScopeExemptionsFollowPaths.bend, scope_law_file): on a LAWS.bend or a
# PROOF.bend its findings are the same for every source, whatever each holds.
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/syntax/bind.bend as Bind
import ../src/paths.bend as Paths
import ../src/src.bend as Src
import ../src/syntax/tree.bend as Tree
import ../src/syntax/outline.bend as Outline
import ../src/rules/suspicious/concat.bend as Concat

# LAW: on a LAWS.bend or a PROOF.bend, concat's continuation findings are
# the same for any two sources at that path
law scope_concat_cont:
  for +path: String
  for +text: String
  for +toks: List<&2, Lex.Tok>
  for +tree: Tree.Node
  for +bound: Bind.Bound
  for +items: List<&2, Outline.Item>
  for +text2: String
  for +toks2: List<&2, Lex.Tok>
  for +tree2: Tree.Node
  for +bound2: Bind.Bound
  for +items2: List<&2, Outline.Item>
  for +e: {Paths.is_law_file(path) == True{} : Bool}
  {Concat.cont(Src.Src{path, text, toks, tree, bound, items})
    == Concat.cont(Src.Src{path, text2, toks2, tree2, bound2, items2}) : List<&2, F.Finding>}
