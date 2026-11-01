# The editor reads the roles the imports of the tree give the files (src/role.bend's
# marks, as `bolt <path>` reads them) on open and save, the checker's two
# runs, and keeps them with the document: after open or save the documents
# hold the marks read then, and a change keeps the marks as they were, so
# every change is linted with the roles of the last open or save
# (laws/LspPublishesOnDocumentEvents.bend says what each publishes).
import Base
import ../src/lsp/server.bend as Server
import ../src/lsp/docs.bend as Docs
import ../src/lsp/report.bend as Rep
import ../src/lsp/enc.bend as Enc
import ../src/role.bend as Role

# the open documents after a method's work
def keep.docs(ww: Server.Work) -> List<&2, Docs.Doc>:
  Server.Work{_notes, _answer, docs} = ww
  docs

# LAW: after open the documents hold the marks read with it
law open_keeps_marks:
  for +ee: Enc.Enc
  for +uri: String
  for +text: String
  for +ds: List<&2, Rep.Diag>
  for +rs: List<&2, Maybe<&2, String>>
  for +ms: List<&2, Role.Mark>
  for +docs: List<&2, Docs.Doc>
  {Docs.marks(keep.docs(Server.pub.open(ee, uri, text, ds, rs, ms, docs)), uri) == ms : List<&2, Role.Mark>}

# LAW: after save the documents hold the marks read with it
law save_keeps_marks:
  for +ee: Enc.Enc
  for +uri: String
  for +ds: List<&2, Rep.Diag>
  for +rs: List<&2, Maybe<&2, String>>
  for +ms: List<&2, Role.Mark>
  for +docs: List<&2, Docs.Doc>
  {Docs.marks(keep.docs(Server.pub.save(ee, uri, ds, rs, ms, docs)), uri) == ms : List<&2, Role.Mark>}

# LAW: a change keeps the marks as they were
law change_keeps_marks:
  for +ee: Enc.Enc
  for +uri: String
  for +text: String
  for +rs: List<&2, Maybe<&2, String>>
  for +docs: List<&2, Docs.Doc>
  {Docs.marks(keep.docs(Server.pub.change(ee, uri, text, rs, docs)), uri) == Docs.marks(docs, uri)
    : List<&2, Role.Mark>}
