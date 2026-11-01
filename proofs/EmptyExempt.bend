# proofs of laws/EmptyExempt.bend
import Base
import ../src/finding.bend as F
import ../src/rules/tokens.bend as T
import ../src/paths.bend as Paths
import ../src/lazy/lazy.bend as Lazy
import ../src/rules/suspicious/empty.bend as Empty
import ../laws/EmptyExempt.bend as Laws

def Laws.empty_exempt(path, _text, toks, _tree, _bound, _items, e):
  %Equal.sym(Bool, Paths.is_law_file(path), True{}, e) : {Lazy.stop(List<&2, F.Finding>, _, [],
    _u => Empty.walk(T.sig(toks), path, False{})) == Nil{}
    : List<&2, F.Finding>}
  {==}
