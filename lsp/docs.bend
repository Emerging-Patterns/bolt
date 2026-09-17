# lsp/docs: the open documents, by URI: what the editor shows, saved or not.
import Base

type Doc is Data:
  Doc{uri: String, text: String}

def del(docs: List<&2, Doc>, +uri: String) -> List<&2, Doc>:
  match docs:
    case Nil{}:
      Nil{}
    case Con{Doc{+u, t}, r}:
      +rest = del(r, uri)
      Bool.pick(List<&2, Doc>, String.eq(u, uri), rest, Doc{u, t} <> rest)

def set(docs: List<&2, Doc>, +uri: String, text: String) -> List<&2, Doc>:
  Doc{uri, text} <> del(docs, uri)

def get(docs: List<&2, Doc>, +uri: String) -> Maybe<&2, String>:
  match docs:
    case Nil{}:
      None{}
    case Con{Doc{u, t}, r}:
      Bool.pick(Maybe<&2, String>, String.eq(u, uri), Some{t}, get(r, uri))
