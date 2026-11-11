# proofs of laws/BlankExempt.bend
import Base
import ../src/finding.bend as F
import ../src/rules/tokens.bend as T
import ../src/paths.bend as Paths
import ../src/lazy/lazy.bend as Lazy
import ../src/rules/style/blank.bend as Blank
import ../laws/BlankExempt.bend as Laws

def Laws.blank_exempt(path, _text, toks, _tree, _bound, _items, e):
  %Equal.sym(Bool, Paths.is_law_file(path), True{}, e) : {Lazy.stop(List<&2, F.Finding>, _, [],
    _u => Blank.walk(T.sig(toks), path, False{})) == Nil{}
    : List<&2, F.Finding>}
  {==}
