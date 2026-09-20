# lsp/docs: the open documents, by URI: what the editor shows, saved or not,
# and the checker's last word on each (its errors come from the file on disk,
# the linter's warnings from the text, so both are needed to publish).
import Base
import ../../lazy/lazy.bend as Lazy
import ./report.bend as Rep

# an open document: its URI, the text the editor shows, the checker's errors
# from its last run
type Doc is Data:
  Doc{uri: String, text: String, errors: List<&2, Rep.Diag>}

# the documents without the one at a URI
def del(docs: List<&2, Doc>, +uri: String) -> List<&2, Doc>:
  match docs:
    case Nil{}:
      Nil{}
    case Con{Doc{+u, t, e}, r}:
      +rest = del(r, uri)
      Bool.pick(List<&2, Doc>, String.eq(u, uri), rest, Doc{u, t, e} <> rest)

# the checker's errors for a document, none when it is not open
def errors(docs: List<&2, Doc>, +uri: String) -> List<&2, Rep.Diag>:
  match docs:
    case Nil{}:
      Nil{}
    case Con{Doc{u, t, e}, r}:
      Lazy.stop(List<&2, Rep.Diag>, String.eq(u, uri), e, _u => errors(r, uri))

# a document's text set (opened, or changed); its errors stay
def set(+docs: List<&2, Doc>, +uri: String, text: String) -> List<&2, Doc>:
  Doc{uri, text, errors(docs, uri)} <> del(docs, uri)

# the text of an open document, when it is open
def get(docs: List<&2, Doc>, +uri: String) -> Maybe<&2, String>:
  match docs:
    case Nil{}:
      None{}
    case Con{Doc{u, t, e}, r}:
      Lazy.stop(Maybe<&2, String>, String.eq(u, uri), Some{t}, _u => get(r, uri))

# a document's errors set, from a run of the checker
def set_errors(+docs: List<&2, Doc>, +uri: String, errors: List<&2, Rep.Diag>) -> List<&2, Doc>:
  Doc{uri, Maybe.default(&2, String, get(docs, uri), ""), errors} <> del(docs, uri)
