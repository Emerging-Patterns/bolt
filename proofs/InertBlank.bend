# proofs of laws/InertBlank.bend
import Base
import ../src/syntax/lex.bend as Lex
import ../src/finding.bend as F
import ../src/rules/tokens.bend as T
import ../src/paths.bend as Paths
import ../src/lazy/lazy.bend as Lazy
import ../src/rules/style/blank.bend as Blank
import ../laws/InertBlank.bend as Laws

def Laws.inert_blank(path, _text, toks, _tree, _bound, _items, _text2, toks2, _tree2, _bound2, _items2, e):
  Equal.cong(List<&2, Lex.Tok>, List<&2, F.Finding>,
    z => Lazy.stop(List<&2, F.Finding>, Paths.is_law_file(path), [], _u => Blank.walk(z, path, False{})),
    T.sig(toks), T.sig(toks2), e)
