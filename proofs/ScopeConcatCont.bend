# proofs of laws/ScopeConcatCont.bend
import Base
import ../src/finding.bend as F
import ../src/src.bend as Src
import ../src/rules/suspicious/concat.bend as Concat
import ../laws/ConcatReportsContinuationAppend.bend as L1
import ../laws/ScopeConcatCont.bend as Laws

def Laws.scope_concat_cont(path, text, toks, tree, bound, items, text2, toks2, tree2, bound2, items2, e):
  Equal.trans(List<&2, F.Finding>, Concat.cont(Src.Src{path, text, toks, tree, bound, items}), Nil{},
    Concat.cont(Src.Src{path, text2, toks2, tree2, bound2, items2}),
    L1.concat_cont_exempt(path, text, toks, tree, bound, items, e),
    Equal.sym(List<&2, F.Finding>, Concat.cont(Src.Src{path, text2, toks2, tree2, bound2, items2}), Nil{},
      L1.concat_cont_exempt(path, text2, toks2, tree2, bound2, items2, e)))
