# proofs of laws/PrefixExempt.bend
import Base
import ../src/finding.bend as F
import ../src/rules/tokens.bend as T
import ../src/paths.bend as Paths
import ../src/lazy/lazy.bend as Lazy
import ../src/rules/suspicious/prefix.bend as Prefix
import ../laws/PrefixExempt.bend as Laws

def Laws.prefix_exempt(path, _text, toks, _tree, _bound, _items, e):
  %Equal.sym(Bool, Paths.is_law_file(path), True{}, e) : {Lazy.stop(List<&2, F.Finding>, _, [],
    _u => Prefix.walk(T.sig(toks), path)) == Nil{}
    : List<&2, F.Finding>}
  {==}
