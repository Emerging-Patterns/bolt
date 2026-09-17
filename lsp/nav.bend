# lsp/nav: from a name to the item it names. A name `Alias.rest`, where Alias
# is an import of the document, is `rest` in that file; any other name is an
# item of the document, or else of Base. Open documents are read from the
# store (what the editor shows), everything else through the files service.
import Base
import ../syntax/outline.bend as Outline
import ../syntax/word.bend as Word
import ../syntax/scope.bend as Scope
import ./files/service.bend as F
import ./docs.bend as Docs
import ./path.bend as Path
import ./proto.bend as Proto

# what a name names: an item and the document it lives in, or a parameter or
# local of the document itself
type Found is Data:
  Found{uri: String, item: Outline.Item}
  Here{uri: String, local: Scope.Local}

def found(m: Maybe<&2, Outline.Item>, uri: String) -> Maybe<&2, Found>:
  match m:
    case None{}:
      None{}
    case Some{item}:
      Some{Found{uri, item}}

def load.miss(~fs: F.Files, open: Maybe<&2, String>, path: String) -> IO(String):
  match open:
    case Some{text}:
      IO.pure(String, text)
    case None{}:
      do IO<String>:
        r : Maybe<&2, String> <- F.read(fs, path)
        return Maybe.default(&2, String, r, "")

# a document's text: the open one, or the file's; "" when there is neither
def load(~fs: F.Files, docs: List<&2, Docs.Doc>, uri: String, path: String) -> IO(String):
  load.miss(~fs, Docs.get(docs, uri), path)

def in_file(~fs: F.Files, docs: List<&2, Docs.Doc>, +path: String, name: String) -> IO(Maybe<&2, Found>):
  do IO<Maybe<&2, Found>>:
    text : String <- load(~fs, docs, "file://" ++ path, path)
    return found(Outline.find(Outline.items(text), name), "file://" ++ path)

def in_base(~fs: F.Files, docs: List<&2, Docs.Doc>, name: String) -> IO(Maybe<&2, Found>):
  do IO<Maybe<&2, Found>>:
    path : String <- F.base_path(fs)
    in_file(~fs, docs, path, name)

def own(~fs: F.Files, m: Maybe<&2, Outline.Item>, docs: List<&2, Docs.Doc>, uri: String, name: String) ->
  IO(Maybe<&2, Found>):
  match m:
    case Some{item}:
      IO.pure(Maybe<&2, Found>, Some{Found{uri, item}})
    case None{}:
      in_base(~fs, docs, name)

def via(~fs: F.Files, imp: Maybe<&2, String>, docs: List<&2, Docs.Doc>, +uri: String, +name: String,
  items: List<&2, Outline.Item>) -> IO(Maybe<&2, Found>):
  match imp:
    case Some{rel}:
      in_file(~fs, docs, Path.join(Path.dir(Proto.path(uri)), rel), Word.rest(name))
    case None{}:
      own(~fs, Outline.find(items, name), docs, uri, name)

def among(~fs: F.Files, +items: List<&2, Outline.Item>, docs: List<&2, Docs.Doc>, uri: String, +name: String) ->
  IO(Maybe<&2, Found>):
  via(~fs, Outline.import_path(items, Word.head(name)), docs, uri, name, items)

# the item a name in a document names
def resolve(~fs: F.Files, +docs: List<&2, Docs.Doc>, +uri: String, name: String) -> IO(Maybe<&2, Found>):
  do IO<Maybe<&2, Found>>:
    text : String <- load(~fs, docs, uri, Proto.path(uri))
    among(~fs, Outline.items(text), docs, uri, name)

# a parameter or a local shadows any item of the same name
def at.name(~fs: F.Files, l: Maybe<&2, Scope.Local>, docs: List<&2, Docs.Doc>, uri: String, name: String) ->
  IO(Maybe<&2, Found>):
  match l:
    case Some{local}:
      IO.pure(Maybe<&2, Found>, Some{Here{uri, local}})
    case None{}:
      resolve(~fs, docs, uri, name)

def at.word(~fs: F.Files, +name: String, text: String, docs: List<&2, Docs.Doc>, uri: String, line: U32) ->
  IO(Maybe<&2, Found>):
  at.name(~fs, Scope.lookup(text, line, name), docs, uri, name)

def at.in(~fs: F.Files, +text: String, docs: List<&2, Docs.Doc>, uri: String, +line: U32, col: U32) ->
  IO(Maybe<&2, Found>):
  at.word(~fs, Word.at(text, line, col), text, docs, uri, line)

# what the name under a position of a document names
def at(~fs: F.Files, +docs: List<&2, Docs.Doc>, +uri: String, line: U32, col: U32) -> IO(Maybe<&2, Found>):
  do IO<Maybe<&2, Found>>:
    text : String <- load(~fs, docs, uri, Proto.path(uri))
    at.in(~fs, text, docs, uri, line, col)

# the items of a document
def outline(~fs: F.Files, docs: List<&2, Docs.Doc>, +uri: String) -> IO(List<&2, Outline.Item>):
  do IO<List<&2, Outline.Item>>:
    text : String <- load(~fs, docs, uri, Proto.path(uri))
    return Outline.items(text)

# completion
# ----------

def starting_in(~fs: F.Files, docs: List<&2, Docs.Doc>, +path: String, prefix: String, qual: String) ->
  IO(List<&2, Outline.Item>):
  do IO<List<&2, Outline.Item>>:
    text : String <- load(~fs, docs, "file://" ++ path, path)
    return Outline.starting(Outline.items(text), prefix, qual)

# Base is big: it is offered once something is typed
def from_base(~fs: F.Files, typed: Bool, docs: List<&2, Docs.Doc>, prefix: String) -> IO(List<&2, Outline.Item>):
  match typed:
    case False{}:
      IO.pure(List<&2, Outline.Item>, [])
    case True{}:
      do IO<List<&2, Outline.Item>>:
        path : String <- F.base_path(fs)
        starting_in(~fs, docs, path, prefix, "")

# a local as a candidate: its note stands for a signature
def as_items(ls: List<&2, Scope.Local>) -> List<&2, Outline.Item>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{Scope.Local{name, line, col, note, param}, t}:
      Outline.Item{Outline.ILocal{}, name, line, note, Bool.pick(String, param, "parameter", "local"), ""} <> as_items(t)

def unqualified(~fs: F.Files, +items: List<&2, Outline.Item>, docs: List<&2, Docs.Doc>, +prefix: String,
  locals: List<&2, Outline.Item>) -> IO(List<&2, Outline.Item>):
  do IO<List<&2, Outline.Item>>:
    base : List<&2, Outline.Item> <- from_base(~fs, Bool.not(String.is_empty(prefix)), docs, prefix)
    return List.append(&2, Outline.Item, Outline.starting(locals, prefix, ""),
      List.append(&2, Outline.Item, Outline.starting(items, prefix, ""),
        List.append(&2, Outline.Item, Outline.aliases(items, prefix), base)))

# `Alias.re` completes from the file behind the alias; anything else from the
# document, its aliases and Base
def candidates.via(~fs: F.Files, imp: Maybe<&2, String>, items: List<&2, Outline.Item>, docs: List<&2, Docs.Doc>,
  uri: String, +prefix: String, locals: List<&2, Outline.Item>) -> IO(List<&2, Outline.Item>):
  match imp:
    case Some{rel}:
      starting_in(~fs, docs, Path.join(Path.dir(Proto.path(uri)), rel), Word.rest(prefix), Word.head(prefix) ++ ".")
    case None{}:
      unqualified(~fs, items, docs, prefix, locals)

def candidates.among(~fs: F.Files, +items: List<&2, Outline.Item>, docs: List<&2, Docs.Doc>, uri: String,
  +prefix: String, locals: List<&2, Outline.Item>) -> IO(List<&2, Outline.Item>):
  candidates.via(~fs, Outline.import_path(items, Word.head(prefix)), items, docs, uri, prefix, locals)

def candidates.in(~fs: F.Files, +text: String, docs: List<&2, Docs.Doc>, uri: String, prefix: String, line: U32) ->
  IO(List<&2, Outline.Item>):
  candidates.among(~fs, Outline.items(text), docs, uri, prefix, as_items(Scope.visible(text, line)))

# what could complete the prefix typed at a line of a document: the locals
# visible there, then items, each named by the text to insert
def candidates(~fs: F.Files, +docs: List<&2, Docs.Doc>, +uri: String, prefix: String, line: U32) ->
  IO(List<&2, Outline.Item>):
  do IO<List<&2, Outline.Item>>:
    text : String <- load(~fs, docs, uri, Proto.path(uri))
    candidates.in(~fs, text, docs, uri, prefix, line)

def text_of(~fs: F.Files, docs: List<&2, Docs.Doc>, +uri: String) -> IO(String):
  load(~fs, docs, uri, Proto.path(uri))
