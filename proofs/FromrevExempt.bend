# proofs of laws/FromrevExempt.bend
import Base
import ../src/finding.bend as F
import ../src/rules/tokens.bend as T
import ../src/paths.bend as Paths
import ../src/lazy/lazy.bend as Lazy
import ../src/rules/suspicious/fromrev.bend as Fromrev
import ../laws/FromrevExempt.bend as Laws

def Laws.fromrev_exempt(path, _text, toks, _tree, _bound, _items, e):
  %Equal.sym(Bool, Paths.is_law_file(path), True{}, e) : {Lazy.stop(List<&2, F.Finding>, _, [],
    _u => Fromrev.walk(T.sig(toks), path)) == Nil{}
    : List<&2, F.Finding>}
  {==}
