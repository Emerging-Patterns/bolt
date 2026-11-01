# proofs of laws/LspKeepsRoleMarks.bend
import Base
import ../src/lazy/lazy.bend as Lazy
import ../src/lsp/docs.bend as Docs
import ../src/lsp/report.bend as Rep
import ../src/role.bend as Role
import ../laws/LspKeepsRoleMarks.bend as Laws
import ./lemmas/PublishComparisons.bend as M1

# the document just put at the head of the list is the one a lookup of its
# URI finds: its marks
law keep.marks_head:
  for +uri: String
  for -text: String
  for -ds: List<&2, Rep.Diag>
  for -ms: List<&2, Role.Mark>
  for -rest: List<&2, Docs.Doc>
  {Docs.marks(Docs.Doc{uri, text, ds, ms} <> rest, uri) == ms : List<&2, Role.Mark>}

def keep.marks_head(uri, _text, _ds, ms, rest):
  e = Equal.sym(Bool, String.eq(uri, uri), True{}, M1.pub.seq_refl(uri))
  %e : {Lazy.stop(List<&2, Role.Mark>, _, ms, _u => Docs.marks(rest, uri)) == ms : List<&2, Role.Mark>}
  {==}

def Laws.open_keeps_marks(_ee, uri, text, ds, _rs, ms, docs):
  keep.marks_head(uri, Maybe.default(&2, String, Docs.get(Docs.set(docs, uri, text), uri), ""), ds, ms,
    Docs.del(Docs.set(docs, uri, text), uri))

def Laws.save_keeps_marks(_ee, uri, ds, _rs, ms, docs):
  keep.marks_head(uri, Maybe.default(&2, String, Docs.get(docs, uri), ""), ds, ms, Docs.del(docs, uri))

def Laws.change_keeps_marks(_ee, uri, text, _rs, docs):
  keep.marks_head(uri, text, Docs.errors(docs, uri), Docs.marks(docs, uri), Docs.del(docs, uri))
