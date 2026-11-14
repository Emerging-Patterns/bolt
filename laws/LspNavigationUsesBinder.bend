# Hover, definition, references and completion answer from the binder
# (laws/BinderResolvesInnermostFirst.bend) over the open text and its relative imports.
import Base
import ../src/lsp/docs.bend as Docs
import ../src/lsp/proto.bend as Proto
import ../src/lsp/nav.bend as Nav
import ../src/lsp/files/service.bend as Fs
import ../src/syntax/bind.bend as Bind
import ../src/syntax/outline.bend as Outline
import ../src/syntax/word.bend as Word
import ../src/lsp/path.bend as Path

# navigation
# ----------

# Hover, definition, references and completion read an open document as the
# text the editor shows, and answer from syntax's binder over it
# (laws/BinderResolvesInnermostFirst.bend). The laws below hold for every files service and every set of
# open documents, and each answer is run to its end (R and k are whatever
# the loop does next). Definition answers a use as the binder resolved it:
# a binder, an item of the document (before any alias), a name in the file
# an import names (relative to the document, and read from the editor when
# open), or Base; hover on a use answers the same.

# LAW: an open document is read as the text the editor shows, whatever the
# files service holds
law nav_open_text:
  for -fs: Fs.Files
  for +docs: List<&2, Docs.Doc>
  for +uri: String
  for +text: String
  for h: {Docs.get(docs, uri) == Some{text} : Maybe<&2, String>}
  for -R: Type
  for -k: String -> IO.OP<R>
  {Nav.text_of(~fs, docs, uri, R, k) == k(text) : IO.OP<R>}

# a binder the binder found, in the document
def nav.local(m: Maybe<&2, Bind.Bind>, uri: String) -> Maybe<&2, Nav.Found>:
  match m:
    case None{}:
      None{}
    case Some{b}:
      Some{Nav.Here{uri, b}}

# the binders the binder found in a text
def nav.binds(b: Bind.Bound) -> List<&2, Bind.Bind>:
  Bind.Bound{binds, _uses, _scopes} = b
  binds

# LAW: definition on a binder of the open text is that binder
law nav_definition_binder:
  for -fs: Fs.Files
  for +docs: List<&2, Docs.Doc>
  for +uri: String
  for +text: String
  for h: {Docs.get(docs, uri) == Some{text} : Maybe<&2, String>}
  for +line: U32
  for +col: U32
  for +b: Bind.Bind
  for hs: {Bind.at(Bind.bound(text), line, col) == Some{Bind.SBind{b}} : Maybe<&2, Bind.Site>}
  for -R: Type
  for -k: Maybe<&2, Nav.Found> -> IO.OP<R>
  {Nav.at(~fs, docs, uri, line, col, R, k) == k(Some{Nav.Here{uri, b}}) : IO.OP<R>}

# LAW: definition on a use the binder resolves to a binder of the open text
# lands on that binder
law nav_definition_local:
  for -fs: Fs.Files
  for +docs: List<&2, Docs.Doc>
  for +uri: String
  for +text: String
  for h: {Docs.get(docs, uri) == Some{text} : Maybe<&2, String>}
  for +line: U32
  for +col: U32
  for +n: String
  for +l: U32
  for +c: U32
  for +tl: U32
  for +tc: U32
  for hs: {Bind.at(Bind.bound(text), line, col) == Some{Bind.SUse{Bind.Use{n, l, c, Bind.TLocal{tl, tc}}}}
    : Maybe<&2, Bind.Site>}
  for -R: Type
  for -k: Maybe<&2, Nav.Found> -> IO.OP<R>
  {Nav.at(~fs, docs, uri, line, col, R, k) == k(nav.local(Bind.binder(nav.binds(Bind.bound(text)), tl, tc), uri))
    : IO.OP<R>}

# LAW: definition on a use the binder resolves to an item of the open text
# lands on that item, before any import alias is looked at
law nav_definition_item:
  for -fs: Fs.Files
  for +docs: List<&2, Docs.Doc>
  for +uri: String
  for +text: String
  for h: {Docs.get(docs, uri) == Some{text} : Maybe<&2, String>}
  for +line: U32
  for +col: U32
  for +n: String
  for +l: U32
  for +c: U32
  for +item: String
  for hs: {Bind.at(Bind.bound(text), line, col) == Some{Bind.SUse{Bind.Use{n, l, c, Bind.TItem{item}}}}
    : Maybe<&2, Bind.Site>}
  for +it: Outline.Item
  for hi: {Outline.find(Outline.items(text), item) == Some{it} : Maybe<&2, Outline.Item>}
  for -R: Type
  for -k: Maybe<&2, Nav.Found> -> IO.OP<R>
  {Nav.at(~fs, docs, uri, line, col, R, k) == k(Some{Nav.Found{uri, it}}) : IO.OP<R>}

# LAW: definition on a use the binder resolves to `rest` behind an import
# alias is `rest` in the file that import names, relative to the document
law nav_definition_import:
  for -fs: Fs.Files
  for +docs: List<&2, Docs.Doc>
  for +uri: String
  for +text: String
  for h: {Docs.get(docs, uri) == Some{text} : Maybe<&2, String>}
  for +line: U32
  for +col: U32
  for +n: String
  for +l: U32
  for +c: U32
  for +alias: String
  for +rest: String
  for hs: {Bind.at(Bind.bound(text), line, col) == Some{Bind.SUse{Bind.Use{n, l, c, Bind.TQual{alias, rest}}}}
    : Maybe<&2, Bind.Site>}
  for +rel: String
  for hi: {Outline.import_path(Outline.items(text), alias) == Some{rel} : Maybe<&2, String>}
  for -R: Type
  for -k: Maybe<&2, Nav.Found> -> IO.OP<R>
  {Nav.at(~fs, docs, uri, line, col, R, k)
    == Nav.in_file(~fs, docs, Path.join(Path.dir(Proto.path(uri)), rel), rest, R, k) : IO.OP<R>}

# LAW: definition on a use the binder leaves free, which no item of the open
# text names, is looked up in Base
law nav_definition_free:
  for -fs: Fs.Files
  for +docs: List<&2, Docs.Doc>
  for +uri: String
  for +text: String
  for h: {Docs.get(docs, uri) == Some{text} : Maybe<&2, String>}
  for +line: U32
  for +col: U32
  for +n: String
  for +l: U32
  for +c: U32
  for hs: {Bind.at(Bind.bound(text), line, col) == Some{Bind.SUse{Bind.Use{n, l, c, Bind.TFree{}}}}
    : Maybe<&2, Bind.Site>}
  for hi: {Outline.find(Outline.items(text), n) == None{} : Maybe<&2, Outline.Item>}
  for -R: Type
  for -k: Maybe<&2, Nav.Found> -> IO.OP<R>
  {Nav.at(~fs, docs, uri, line, col, R, k) == Nav.in_base(~fs, docs, n, R, k) : IO.OP<R>}

# LAW: a file behind an import is read, like the document, as the text the
# editor shows when it is open: a name in it is that text's item
law nav_import_open:
  for -fs: Fs.Files
  for +docs: List<&2, Docs.Doc>
  for +path: String
  for +text: String
  for h: {Docs.get(docs, "file://" ++ path) == Some{text} : Maybe<&2, String>}
  for +name: String
  for -R: Type
  for -k: Maybe<&2, Nav.Found> -> IO.OP<R>
  {Nav.in_file(~fs, docs, path, name, R, k) == k(Nav.found(Outline.find(Outline.items(text), name), "file://" ++ path))
    : IO.OP<R>}

# LAW: hover on a use answers what definition answers on it
law nav_hover_use:
  for -fs: Fs.Files
  for +docs: List<&2, Docs.Doc>
  for +uri: String
  for +text: String
  for +h: {Docs.get(docs, uri) == Some{text} : Maybe<&2, String>}
  for +line: U32
  for +col: U32
  for +u: Bind.Use
  for +hs: {Bind.at(Bind.bound(text), line, col) == Some{Bind.SUse{u}} : Maybe<&2, Bind.Site>}
  for -R: Type
  for -k: Maybe<&2, Nav.Found> -> IO.OP<R>
  {Nav.hover(~fs, docs, uri, line, col, R, k) == Nav.at(~fs, docs, uri, line, col, R, k) : IO.OP<R>}

# is a binder of this kind an item's name (a def, law or type)?
def nav.item_kind(kind: Bind.BindKind) -> Bool:
  match kind:
    case Bind.KItem{}:
      True{}
    case _other:
      False{}

# LAW: hover on a binder of the open text that names no item shows that
# binder
law nav_hover_binder:
  for -fs: Fs.Files
  for +docs: List<&2, Docs.Doc>
  for +uri: String
  for +text: String
  for h: {Docs.get(docs, uri) == Some{text} : Maybe<&2, String>}
  for +line: U32
  for +col: U32
  for +name: String
  for +bl: U32
  for +bc: U32
  for +kind: Bind.BindKind
  for +note: String
  for hs: {Bind.at(Bind.bound(text), line, col) == Some{Bind.SBind{Bind.Bind{name, bl, bc, kind, note}}}
    : Maybe<&2, Bind.Site>}
  for hk: {nav.item_kind(kind) == False{} : Bool}
  for -R: Type
  for -k: Maybe<&2, Nav.Found> -> IO.OP<R>
  {Nav.hover(~fs, docs, uri, line, col, R, k) == k(Some{Nav.Here{uri, Bind.Bind{name, bl, bc, kind, note}}})
    : IO.OP<R>}

# LAW: hover on an item's own name shows the item behind the import alias
# its head names, relative to the document (a proof's `def Laws.x` shows
# the law in the file behind `Laws`), and falls back to the document's item
# of that name, then to the binder
law nav_hover_item:
  for -fs: Fs.Files
  for +docs: List<&2, Docs.Doc>
  for +uri: String
  for +text: String
  for +h: {Docs.get(docs, uri) == Some{text} : Maybe<&2, String>}
  for +line: U32
  for +col: U32
  for +name: String
  for +bl: U32
  for +bc: U32
  for +note: String
  for hs: {Bind.at(Bind.bound(text), line, col) == Some{Bind.SBind{Bind.Bind{name, bl, bc, Bind.KItem{}, note}}}
    : Maybe<&2, Bind.Site>}
  for +rel: String
  for hi: {Outline.import_path(Outline.items(text), Word.head(name)) == Some{rel} : Maybe<&2, String>}
  for -R: Type
  for -k: Maybe<&2, Nav.Found> -> IO.OP<R>
  {Nav.hover(~fs, docs, uri, line, col, R, k)
    == Nav.in_file(~fs, docs, Path.join(Path.dir(Proto.path(uri)), rel), Word.rest(name), R,
      m => k(Nav.hover.pick(m, Nav.found(Outline.find(Outline.items(text), name), uri), uri,
        Bind.Bind{name, bl, bc, Bind.KItem{}, note}))) : IO.OP<R>}

# LAW: hover on an item's own name whose head names no import is the
# document's item of that name
law nav_hover_own:
  for -fs: Fs.Files
  for +docs: List<&2, Docs.Doc>
  for +uri: String
  for +text: String
  for +h: {Docs.get(docs, uri) == Some{text} : Maybe<&2, String>}
  for +line: U32
  for +col: U32
  for +name: String
  for +bl: U32
  for +bc: U32
  for +note: String
  for hs: {Bind.at(Bind.bound(text), line, col) == Some{Bind.SBind{Bind.Bind{name, bl, bc, Bind.KItem{}, note}}}
    : Maybe<&2, Bind.Site>}
  for hi: {Outline.import_path(Outline.items(text), Word.head(name)) == None{} : Maybe<&2, String>}
  for +it: Outline.Item
  for hf: {Outline.find(Outline.items(text), name) == Some{it} : Maybe<&2, Outline.Item>}
  for -R: Type
  for -k: Maybe<&2, Nav.Found> -> IO.OP<R>
  {Nav.hover(~fs, docs, uri, line, col, R, k) == k(Some{Nav.Found{uri, it}}) : IO.OP<R>}

# the positions of a binder the binder found: an item's or a constructor's
# declaration and uses, any other binder's own position and its uses'
def nav.bind_sites(kind: Bind.BindKind, +name: String, +l: U32, +c: U32, +b: Bind.Bound) -> Nav.Sites:
  match kind:
    case Bind.KItem{}:
      Nav.Sites{True{}, Bind.item_sites(b, name)}
    case Bind.KCtor{}:
      Nav.Sites{True{}, Bind.item_sites(b, name)}
    case _other:
      Nav.Sites{True{}, Bind.sites(b, l, c)}

# the positions of a use, by what the binder resolved it to: a binder's, an
# item's, or for a name from Base or behind an alias its uses by that name,
# which are not the document's own
def nav.use_sites(tg: Bind.Target, +name: String, +b: Bind.Bound) -> Nav.Sites:
  match tg:
    case Bind.TLocal{tl, tc}:
      Nav.Sites{True{}, Bind.sites(b, tl, tc)}
    case Bind.TItem{item}:
      Nav.Sites{True{}, Bind.item_sites(b, item)}
    case _other:
      Nav.Sites{False{}, Bind.named_sites(b, name)}

# the positions references answers for the site the binder found, and
# whether they are the document's own (only those rename)
def nav.referenced(site: Maybe<&2, Bind.Site>, +b: Bind.Bound) -> Nav.Sites:
  match site:
    case None{}:
      Nav.Sites{False{}, []}
    case Some{Bind.SBind{Bind.Bind{name, l, c, kind, _note}}}:
      nav.bind_sites(kind, name, l, c, b)
    case Some{Bind.SUse{Bind.Use{name, _l, _c, tg}}}:
      nav.use_sites(tg, name, b)

# LAW: references answer from the binder over the open text: the positions
# of the binder, item or name the binder finds at the position
law nav_references:
  for -fs: Fs.Files
  for +docs: List<&2, Docs.Doc>
  for +uri: String
  for +text: String
  for h: {Docs.get(docs, uri) == Some{text} : Maybe<&2, String>}
  for +line: U32
  for +col: U32
  for -R: Type
  for -k: Nav.Sites -> IO.OP<R>
  {Nav.sites(~fs, docs, uri, line, col, R, k)
    == k(nav.referenced(Bind.at(Bind.bound(text), line, col), Bind.bound(text))) : IO.OP<R>}

# the binders the binder has in scope at a line of a text, those that start
# with the prefix, as completion items
def nav.locals(+text: String, +prefix: String, +line: U32) -> List<&2, Outline.Item>:
  Outline.starting(Nav.as_items(Bind.visible(Bind.bound(text), line)), prefix, "")

# what completion offers after the names the binder has in scope: the
# document's items, its aliases, then what Base gave
def nav.after(+text: String, +prefix: String, base: List<&2, Outline.Item>) -> List<&2, Outline.Item>:
  List.append(&2, Outline.Item, Outline.starting(Outline.items(text), prefix, ""),
    List.append(&2, Outline.Item, Outline.aliases(Outline.items(text), prefix), base))

# LAW: completion of a name typed under no import alias of the open text
# offers first the binders the binder has in scope at the line, those that
# start with what is typed, then the document's items, its aliases and Base
law nav_completion:
  for -fs: Fs.Files
  for +docs: List<&2, Docs.Doc>
  for +uri: String
  for +text: String
  for h: {Docs.get(docs, uri) == Some{text} : Maybe<&2, String>}
  for +prefix: String
  for +line: U32
  for hp: {Outline.import_path(Outline.items(text), Word.head(prefix)) == None{} : Maybe<&2, String>}
  for -R: Type
  for -k: List<&2, Outline.Item> -> IO.OP<R>
  {Nav.candidates(~fs, docs, uri, prefix, line, R, k)
    == Nav.from_base(~fs, Bool.not(String.is_empty(prefix)), docs, prefix, R,
      base => k(List.append(&2, Outline.Item, nav.locals(text, prefix, line), nav.after(text, prefix, base))))
    : IO.OP<R>}

# LAW: completion of `Alias.pre`, where Alias is an import of the open text,
# offers the items starting with `pre` of the file the import names,
# relative to the document, each named `Alias.` and the item's name
law nav_completion_import:
  for -fs: Fs.Files
  for +docs: List<&2, Docs.Doc>
  for +uri: String
  for +text: String
  for h: {Docs.get(docs, uri) == Some{text} : Maybe<&2, String>}
  for +prefix: String
  for +line: U32
  for +rel: String
  for hp: {Outline.import_path(Outline.items(text), Word.head(prefix)) == Some{rel} : Maybe<&2, String>}
  for -R: Type
  for -k: List<&2, Outline.Item> -> IO.OP<R>
  {Nav.candidates(~fs, docs, uri, prefix, line, R, k)
    == Nav.starting_in(~fs, docs, Path.join(Path.dir(Proto.path(uri)), rel), Word.rest(prefix),
        Word.head(prefix) ++ ".",
      R, k) : IO.OP<R>}

# LAW: a directory and a path relative to it are one absolute path: their
# segments with `.` and `..` resolved, joined by `/` under a leading `/`
law path_joins_under_a_slash:
  for dir: String
  for rel: String
  {Path.join(dir, rel)
    == "/" ++ String.join(List.reverse(&2, String, Path.norm(String.split(dir ++ "/" ++ rel, '/'), [])), "/")
    : String}

# LAW: a file's directory is its path with `..` joined on
law path_dir_is_one_up:
  for path: String
  {Path.dir(path) == Path.join(path, "..") : String}

# LAW: a file is named to the editor by its path under the `file://` scheme
law uri_of_a_path:
  for path: String
  {Nav.uri_of(path) == "file://" ++ path : String}
