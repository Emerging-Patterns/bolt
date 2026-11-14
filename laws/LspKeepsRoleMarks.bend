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
import ../src/lint/world.bend as World

# the open documents after a method's work
def keep.docs(w: Server.Work) -> List<&2, Docs.Doc>:
  Server.Work{_notes, _answer, docs} = w
  docs

# LAW: after open the documents hold the marks read with it
law open_keeps_marks:
  for +e: Enc.Enc
  for +uri: String
  for +text: String
  for +ds: List<&2, Rep.Diag>
  for +rs: List<&2, Maybe<&2, String>>
  for +ms: List<&2, Role.Mark>
  for +docs: List<&2, Docs.Doc>
  {Docs.marks(keep.docs(Server.pub.open(e, uri, text, ds, rs, ms, docs)), uri) == ms : List<&2, Role.Mark>}

# LAW: after save the documents hold the marks read with it
law save_keeps_marks:
  for +e: Enc.Enc
  for +uri: String
  for +ds: List<&2, Rep.Diag>
  for +rs: List<&2, Maybe<&2, String>>
  for +ms: List<&2, Role.Mark>
  for +docs: List<&2, Docs.Doc>
  {Docs.marks(keep.docs(Server.pub.save(e, uri, ds, rs, ms, docs)), uri) == ms : List<&2, Role.Mark>}

# LAW: a change keeps the marks as they were
law change_keeps_marks:
  for +e: Enc.Enc
  for +uri: String
  for +text: String
  for +rs: List<&2, Maybe<&2, String>>
  for +docs: List<&2, Docs.Doc>
  {Docs.marks(keep.docs(Server.pub.change(e, uri, text, rs, docs)), uri) == Docs.marks(docs, uri)
    : List<&2, Role.Mark>}

# LAW: the answers the server reads for the graph join the ones it already
# has, after them: an earlier answer to a question stays the first one found
law world_keeps_earlier_answers_first:
  for paths: List<&2, String>
  for cwd: String
  for replies: List<&2, World.Reply>
  for rs: List<&2, World.Reply>
  {Server.pub.world.more(World.World{paths, cwd, replies}, rs)
    == World.World{paths, cwd, List.append(&2, World.Reply, replies, rs)} : World.World}
