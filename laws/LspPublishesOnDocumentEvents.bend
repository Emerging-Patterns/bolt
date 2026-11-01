# Open and save publish checker plus lint, each file told its role among the
# marks read with the checker's run; change publishes lint, told the marks
# kept, plus the last checker result; close publishes an empty list; an open bolt.bend gets no
# lint.
import Base
import ../src/lsp/server.bend as Server
import ../src/lsp/docs.bend as Docs
import ../src/lsp/report.bend as Rep
import ../src/lsp/proto.bend as Proto
import ../src/finding.bend as F
import ../src/lint/plan.bend as Plan
import ../src/lsp/enc.bend as Enc
import ../src/role.bend as Role

# publishing
# ----------

# the notifications a method's work sends
def pub.notes(ww: Server.Work) -> List<&2, String>:
  Server.Work{notes, _answer, _docs} = ww
  notes

# the open documents after a method's work
def pub.docs(ww: Server.Work) -> List<&2, Docs.Doc>:
  Server.Work{_notes, _answer, docs} = ww
  docs

# LAW: open publishes the checker's errors plus the lint of the text opened
law open_publishes:
  for +ee: Enc.Enc
  for +uri: String
  for +text: String
  for +ds: List<&2, Rep.Diag>
  for +rs: List<&2, Maybe<&2, String>>
  for +ms: List<&2, Role.Mark>
  for +docs: List<&2, Docs.Doc>
  {pub.notes(Server.pub.open(ee, uri, text, ds, rs, ms, docs))
    == [Server.pub.note(Enc.cols(ee, text), uri, ds, Server.pub.lint(Proto.path(uri), text, rs, ms))]
    : List<&2, String>}

# LAW: save publishes the checker's new errors plus the lint of the text the
# editor shows
law save_publishes:
  for +ee: Enc.Enc
  for +uri: String
  for +ds: List<&2, Rep.Diag>
  for +rs: List<&2, Maybe<&2, String>>
  for +ms: List<&2, Role.Mark>
  for +docs: List<&2, Docs.Doc>
  {pub.notes(Server.pub.save(ee, uri, ds, rs, ms, docs))
    == [Server.pub.note(Enc.cols(ee, Maybe.default(&2, String, Docs.get(docs, uri), "")), uri, ds,
      Server.pub.lint(Proto.path(uri), Maybe.default(&2, String, Docs.get(docs, uri), ""), rs, ms))]
    : List<&2, String>}

# LAW: change publishes the lint of the new text plus the checker's errors
# the documents hold for it
law change_publishes:
  for +ee: Enc.Enc
  for +uri: String
  for +text: String
  for +rs: List<&2, Maybe<&2, String>>
  for +docs: List<&2, Docs.Doc>
  {pub.notes(Server.pub.change(ee, uri, text, rs, docs))
    == [Server.pub.note(Enc.cols(ee, text), uri, Docs.errors(docs, uri),
      Server.pub.lint(Proto.path(uri), text, rs, Docs.marks(docs, uri)))] : List<&2, String>}

# LAW: after open the documents hold the errors it published and the text
# opened
law open_keeps:
  for +ee: Enc.Enc
  for +uri: String
  for +text: String
  for +ds: List<&2, Rep.Diag>
  for +rs: List<&2, Maybe<&2, String>>
  for +ms: List<&2, Role.Mark>
  for +docs: List<&2, Docs.Doc>
  {Docs.errors(pub.docs(Server.pub.open(ee, uri, text, ds, rs, ms, docs)), uri) == ds : List<&2, Rep.Diag>}
    & {Docs.get(pub.docs(Server.pub.open(ee, uri, text, ds, rs, ms, docs)), uri) == Some{text} : Maybe<&2, String>}

# LAW: after save the documents hold the errors it published
law save_keeps:
  for +ee: Enc.Enc
  for +uri: String
  for +ds: List<&2, Rep.Diag>
  for +rs: List<&2, Maybe<&2, String>>
  for +ms: List<&2, Role.Mark>
  for +docs: List<&2, Docs.Doc>
  {Docs.errors(pub.docs(Server.pub.save(ee, uri, ds, rs, ms, docs)), uri) == ds : List<&2, Rep.Diag>}

# LAW: change keeps the checker's errors as they were, so every change
# publishes the last checker result, and keeps the new text
law change_keeps:
  for +ee: Enc.Enc
  for +uri: String
  for +text: String
  for +rs: List<&2, Maybe<&2, String>>
  for +docs: List<&2, Docs.Doc>
  {Docs.errors(pub.docs(Server.pub.change(ee, uri, text, rs, docs)), uri) == Docs.errors(docs, uri)
    : List<&2, Rep.Diag>}
    & {Docs.get(pub.docs(Server.pub.change(ee, uri, text, rs, docs)), uri) == Some{text} : Maybe<&2, String>}

# LAW: close publishes an empty list, and forgets the document's errors
law close_publishes:
  for +ee: Enc.Enc
  for +uri: String
  for +docs: List<&2, Docs.Doc>
  {pub.notes(Server.pub.close(ee, uri, docs)) == [Server.pub.note(Enc.cols(ee, ""), uri, [], [])] : List<&2, String>}
    & {Docs.errors(pub.docs(Server.pub.close(ee, uri, docs)), uri) == [] : List<&2, Rep.Diag>}

# LAW: an open bolt.bend gets no lint, whatever its text and the candidates
law config_unlinted:
  for +path: String
  for h: {Plan.is_config(path) == True{} : Bool}
  for text: String
  for rs: List<&2, Maybe<&2, String>>
  for ms: List<&2, Role.Mark>
  {Server.pub.lint(path, text, rs, ms) == [] : List<&2, F.Graded>}
