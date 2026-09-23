# lsp/nav: from a name to the item it names. A name `Alias.rest`, where Alias
# is an import of the document, is `rest` in that file; any other name is an
# item of the document, or else of Base. Open documents are read from the
# store (what the editor shows), everything else through the files service.
import Base
import ../../syntax/outline.bend as Outline
import ../../syntax/word.bend as Word
import ../../syntax/bind.bend as Bind
import ./files/service.bend as F
import ./docs.bend as Docs
import ./path.bend as Path
import ./proto.bend as Proto

# what a name names: an item and the document it lives in, or a binder of
# the document itself (a parameter, a local, a field, ..)
type Found is Data:
  Found{uri: String, item: Outline.Item}
  Here{uri: String, bind: Bind.Bind}

# an item, when there is one, in a document
def found(mm: Maybe<&2, Outline.Item>, uri: String) -> Maybe<&2, Found>:
  match mm:
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

# the item of a name in a file
def in_file(~fs: F.Files, docs: List<&2, Docs.Doc>, +path: String, name: String) -> IO(Maybe<&2, Found>):
  do IO<Maybe<&2, Found>>:
    text : String <- load(~fs, docs, "file://" ++ path, path)
    return found(Outline.find(Outline.items(text), name), "file://" ++ path)

# the item of a name in Base
def in_base(~fs: F.Files, docs: List<&2, Docs.Doc>, name: String) -> IO(Maybe<&2, Found>):
  do IO<Maybe<&2, Found>>:
    path : String <- F.base_path(fs)
    in_file(~fs, docs, path, name)

# an item of the document, else of Base
def own(
  ~fs: F.Files,
  mm: Maybe<&2, Outline.Item>,
  docs: List<&2, Docs.Doc>,
  uri: String,
  name: String
) -> IO(Maybe<&2, Found>):
  match mm:
    case Some{item}:
      IO.pure(Maybe<&2, Found>, Some{Found{uri, item}})
    case None{}:
      in_base(~fs, docs, name)

# through an import alias when the name has one, else the document's own
def via(
  ~fs: F.Files,
  imp: Maybe<&2, String>,
  docs: List<&2, Docs.Doc>,
  +uri: String,
  +name: String,
  items: List<&2, Outline.Item>
) -> IO(Maybe<&2, Found>):
  match imp:
    case Some{rel}:
      in_file(~fs, docs, Path.join(Path.dir(Proto.path(uri)), rel), Word.rest(name))
    case None{}:
      own(~fs, Outline.find(items, name), docs, uri, name)

# a name against a document's items
def among(
  ~fs: F.Files,
  +items: List<&2, Outline.Item>,
  docs: List<&2, Docs.Doc>,
  uri: String,
  +name: String
) -> IO(Maybe<&2, Found>):
  via(~fs, Outline.import_path(items, Word.head(name)), docs, uri, name, items)

# the item a name in a document names
def resolve(~fs: F.Files, +docs: List<&2, Docs.Doc>, +uri: String, name: String) -> IO(Maybe<&2, Found>):
  do IO<Maybe<&2, Found>>:
    text : String <- load(~fs, docs, uri, Proto.path(uri))
    among(~fs, Outline.items(text), docs, uri, name)

# a binder, when there is one, in a document
def here(mm: Maybe<&2, Bind.Bind>, uri: String) -> Maybe<&2, Found>:
  match mm:
    case None{}:
      None{}
    case Some{b}:
      Some{Here{uri, b}}

# a name behind an import alias: `rest` in the file the import names,
# relative to the document; the document's own item when the outline has no
# import of that alias
def at.qual(
  ~fs: F.Files,
  imp: Maybe<&2, String>,
  rest: String,
  items: List<&2, Outline.Item>,
  docs: List<&2, Docs.Doc>,
  +uri: String,
  +name: String
) -> IO(Maybe<&2, Found>):
  match imp:
    case Some{rel}:
      in_file(~fs, docs, Path.join(Path.dir(Proto.path(uri)), rel), rest)
    case None{}:
      own(~fs, Outline.find(items, name), docs, uri, name)

# a use, by what the binder resolved it to: a binder of the document is that
# binder; an item of the document is that item, before any alias; a name
# behind an alias is looked up in the file the import names; a free name is
# the document's item of that name, else Base's
def at.target(
  ~fs: F.Files,
  tg: Bind.Target,
  +name: String,
  binds: List<&2, Bind.Bind>,
  +items: List<&2, Outline.Item>,
  docs: List<&2, Docs.Doc>,
  +uri: String
) -> IO(Maybe<&2, Found>):
  match tg:
    case Bind.TLocal{tl, tc}:
      IO.pure(Maybe<&2, Found>, here(Bind.binder(binds, tl, tc), uri))
    case Bind.TItem{+item}:
      own(~fs, Outline.find(items, item), docs, uri, item)
    case Bind.TQual{alias, rest}:
      at.qual(~fs, Outline.import_path(items, alias), rest, items, docs, uri, name)
    case Bind.TFree{}:
      own(~fs, Outline.find(items, name), docs, uri, name)

# a binder of the document is answered from the document, and a use as the
# binder resolved it; nothing at all falls back to the word under the cursor
# (a half-typed name)
def at.site(
  ~fs: F.Files,
  site: Maybe<&2, Bind.Site>,
  binds: List<&2, Bind.Bind>,
  items: List<&2, Outline.Item>,
  docs: List<&2, Docs.Doc>,
  +uri: String,
  name: String
) -> IO(Maybe<&2, Found>):
  match site:
    case Some{Bind.SBind{b}}:
      IO.pure(Maybe<&2, Found>, Some{Here{uri, b}})
    case Some{Bind.SUse{Bind.Use{n, _l, _c, tg}}}:
      at.target(~fs, tg, n, binds, items, docs, uri)
    case None{}:
      resolve(~fs, docs, uri, name)

def at.bound(
  ~fs: F.Files,
  bb: Bind.Bound,
  items: List<&2, Outline.Item>,
  docs: List<&2, Docs.Doc>,
  uri: String,
  name: String,
  +line: U32,
  +col: U32
) -> IO(Maybe<&2, Found>):
  Bind.Bound{+binds, uses, scopes} = bb
  at.site(~fs, Bind.at(Bind.Bound{binds, uses, scopes}, line, col), binds, items, docs, uri, name)

def at.in(
  ~fs: F.Files,
  +text: String,
  docs: List<&2, Docs.Doc>,
  uri: String,
  +line: U32,
  +col: U32
) -> IO(Maybe<&2, Found>):
  at.bound(~fs, Bind.bound(text), Outline.items(text), docs, uri, Word.at(text, line, col), line, col)

# what the name under a position of a document names
def at(~fs: F.Files, +docs: List<&2, Docs.Doc>, +uri: String, line: U32, col: U32) -> IO(Maybe<&2, Found>):
  do IO<Maybe<&2, Found>>:
    text : String <- load(~fs, docs, uri, Proto.path(uri))
    at.in(~fs, text, docs, uri, line, col)

# the binder, when the outline has nothing for that name
def hover.binder(mm: Maybe<&2, Found>, uri: String, bb: Bind.Bind) -> Maybe<&2, Found>:
  match mm:
    case Some{f}:
      Some{f}
    case None{}:
      Some{Here{uri, bb}}

# an outline item when the name resolved, else one in this document, else the
# binder. A comment above a law stays on that law: a file header separated by
# an import or a blank line is not part of it
def hover.pick(mm: Maybe<&2, Found>, local: Maybe<&2, Found>, uri: String, bb: Bind.Bind) -> Maybe<&2, Found>:
  match mm:
    case Some{f}:
      Some{f}
    case None{}:
      hover.binder(local, uri, bb)

# the outline item a top-level name hovers as. `Alias.law` is the law in the
# file behind Alias (the comment lives there); a bare name is this document's
def hover.item(
  ~fs: F.Files,
  +name: String,
  items: List<&2, Outline.Item>,
  docs: List<&2, Docs.Doc>,
  +uri: String,
  bb: Bind.Bind
) -> IO(Maybe<&2, Found>):
  do IO<Maybe<&2, Found>>:
    m : Maybe<&2, Found> <- resolve(~fs, docs, uri, name)
    return hover.pick(m, found(Outline.find(items, name), uri), uri, bb)

# a def, law or type is its outline item; any other binder is itself
def hover.kind(
  ~fs: F.Files,
  kind: Bind.BindKind,
  name: String,
  items: List<&2, Outline.Item>,
  docs: List<&2, Docs.Doc>,
  uri: String,
  bb: Bind.Bind
) -> IO(Maybe<&2, Found>):
  match kind:
    case Bind.KItem{}:
      hover.item(~fs, name, items, docs, uri, bb)
    case other:
      IO.pure(Maybe<&2, Found>, Some{Here{uri, bb}})

# the binder under the cursor, read for hover
def hover.bind(
  ~fs: F.Files,
  bb: Bind.Bind,
  items: List<&2, Outline.Item>,
  docs: List<&2, Docs.Doc>,
  uri: String
) -> IO(Maybe<&2, Found>):
  Bind.Bind{+name, line, col, +kind, note} = bb
  hover.kind(~fs, kind, name, items, docs, uri, Bind.Bind{name, line, col, kind, note})

# a binder of an item is the outline item (signature, then the comment above
# it). A use is answered the same way `at` answers it, so a call keeps the
# callee's doc
def hover.site(
  ~fs: F.Files,
  site: Maybe<&2, Bind.Site>,
  items: List<&2, Outline.Item>,
  +binds: List<&2, Bind.Bind>,
  docs: List<&2, Docs.Doc>,
  uri: String,
  +name: String
) -> IO(Maybe<&2, Found>):
  match site:
    case Some{Bind.SBind{b}}:
      hover.bind(~fs, b, items, docs, uri)
    case other:
      at.site(~fs, site, binds, items, docs, uri, name)

# hover at a binding site of a parsed document
def hover.bound(
  ~fs: F.Files,
  bb: Bind.Bound,
  items: List<&2, Outline.Item>,
  docs: List<&2, Docs.Doc>,
  uri: String,
  name: String,
  +line: U32,
  +col: U32
) -> IO(Maybe<&2, Found>):
  Bind.Bound{+binds, uses, scopes} = bb
  hover.site(~fs, Bind.at(Bind.Bound{binds, uses, scopes}, line, col), items, binds, docs, uri, name)

# hover at a position of a document's text
def hover.in(
  ~fs: F.Files,
  +text: String,
  docs: List<&2, Docs.Doc>,
  uri: String,
  +line: U32,
  +col: U32
) -> IO(Maybe<&2, Found>):
  hover.bound(~fs, Bind.bound(text), Outline.items(text), docs, uri, Word.at(text, line, col), line, col)

# what a hover at a position should show. Definition stays on `at`: an item's
# own name is still that binder
def hover(~fs: F.Files, +docs: List<&2, Docs.Doc>, +uri: String, line: U32, col: U32) -> IO(Maybe<&2, Found>):
  do IO<Maybe<&2, Found>>:
    text : String <- load(~fs, docs, uri, Proto.path(uri))
    hover.in(~fs, text, docs, uri, line, col)

# references and rename
# ---------------------

# the positions a name is at in its document, and whether the name is the
# document's own (a binder, or an item of it) -- only those can be renamed
type Sites is Data:
  Sites{mine: Bool, at: List<&2, Bind.Pos>}

def sites.of(site: Maybe<&2, Bind.Site>, +bb: Bind.Bound) -> Sites:
  match site:
    case None{}:
      Sites{False{}, []}
    case Some{Bind.SBind{Bind.Bind{name, l, c, Bind.KItem{}, note}}}:
      Sites{True{}, Bind.item_sites(bb, name)}
    case Some{Bind.SBind{Bind.Bind{name, l, c, Bind.KCtor{}, note}}}:
      Sites{True{}, Bind.item_sites(bb, name)}
    case Some{Bind.SBind{Bind.Bind{name, l, c, k, note}}}:
      Sites{True{}, Bind.sites(bb, l, c)}
    case Some{Bind.SUse{Bind.Use{n, l, c, Bind.TLocal{tl, tc}}}}:
      Sites{True{}, Bind.sites(bb, tl, tc)}
    case Some{Bind.SUse{Bind.Use{n, l, c, Bind.TItem{name}}}}:
      Sites{True{}, Bind.item_sites(bb, name)}
    case Some{Bind.SUse{Bind.Use{n, l, c, other}}}:
      Sites{False{}, Bind.named_sites(bb, n)}

def sites.in(+text: String, +line: U32, +col: U32) -> Sites:
  +b = Bind.bound(text)
  sites.of(Bind.at(b, line, col), b)

# the positions of the name at a position of a document
def sites(~fs: F.Files, docs: List<&2, Docs.Doc>, +uri: String, line: U32, col: U32) -> IO(Sites):
  do IO<Sites>:
    text : String <- load(~fs, docs, uri, Proto.path(uri))
    return sites.in(text, line, col)

# the items of a document
def outline(~fs: F.Files, docs: List<&2, Docs.Doc>, +uri: String) -> IO(List<&2, Outline.Item>):
  do IO<List<&2, Outline.Item>>:
    text : String <- load(~fs, docs, uri, Proto.path(uri))
    return Outline.items(text)

# completion
# ----------

# the items of a file that start with a prefix, renamed for insertion
def starting_in(
  ~fs: F.Files,
  docs: List<&2, Docs.Doc>,
  +path: String,
  prefix: String,
  qual: String
) -> IO(List<&2, Outline.Item>):
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

# a binder as a candidate: its note stands for a signature
def as_items(ls: List<&2, Bind.Bind>) -> List<&2, Outline.Item>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{Bind.Bind{name, line, col, kind, note}, t}:
      Outline.Item{Outline.ILocal{}, name, line, note, Proto.kind_name(kind), ""} <> as_items(t)

# candidates for a plain prefix: visible names, the document's items, its
# aliases, then Base
def unqualified(
  ~fs: F.Files,
  +items: List<&2, Outline.Item>,
  docs: List<&2, Docs.Doc>,
  +prefix: String,
  locals: List<&2, Outline.Item>
) -> IO(List<&2, Outline.Item>):
  do IO<List<&2, Outline.Item>>:
    base : List<&2, Outline.Item> <- from_base(~fs, Bool.not(String.is_empty(prefix)), docs, prefix)
    return List.append(&2, Outline.Item, Outline.starting(locals, prefix, ""),
      List.append(&2, Outline.Item, Outline.starting(items, prefix, ""),
        List.append(&2, Outline.Item, Outline.aliases(items, prefix), base)))

# `Alias.re` completes from the file behind the alias; anything else from the
# document, its aliases and Base
def candidates.via(
  ~fs: F.Files,
  imp: Maybe<&2, String>,
  items: List<&2, Outline.Item>,
  docs: List<&2, Docs.Doc>,
  uri: String,
  +prefix: String,
  locals: List<&2, Outline.Item>
) -> IO(List<&2, Outline.Item>):
  match imp:
    case Some{rel}:
      starting_in(~fs, docs, Path.join(Path.dir(Proto.path(uri)), rel), Word.rest(prefix), Word.head(prefix) ++ ".")
    case None{}:
      unqualified(~fs, items, docs, prefix, locals)

def candidates.among(
  ~fs: F.Files,
  +items: List<&2, Outline.Item>,
  docs: List<&2, Docs.Doc>,
  uri: String,
  +prefix: String,
  locals: List<&2, Outline.Item>
) -> IO(List<&2, Outline.Item>):
  candidates.via(~fs, Outline.import_path(items, Word.head(prefix)), items, docs, uri, prefix, locals)

def candidates.in(
  ~fs: F.Files,
  +text: String,
  docs: List<&2, Docs.Doc>,
  uri: String,
  prefix: String,
  line: U32
) -> IO(List<&2, Outline.Item>):
  candidates.among(~fs, Outline.items(text), docs, uri, prefix, as_items(Bind.visible(Bind.bound(text), line)))

# what could complete the prefix typed at a line of a document: the locals
# visible there, then items, each named by the text to insert
def candidates(
  ~fs: F.Files,
  +docs: List<&2, Docs.Doc>,
  +uri: String,
  prefix: String,
  line: U32
) -> IO(List<&2, Outline.Item>):
  do IO<List<&2, Outline.Item>>:
    text : String <- load(~fs, docs, uri, Proto.path(uri))
    candidates.in(~fs, text, docs, uri, prefix, line)

# a document's text
def text_of(~fs: F.Files, docs: List<&2, Docs.Doc>, +uri: String) -> IO(String):
  load(~fs, docs, uri, Proto.path(uri))
