# proofs of laws/LspNavigationUsesBinder.bend
import Base
import ../src/lsp/docs.bend as Docs
import ../src/lsp/nav.bend as Nav
import ../src/lsp/proto.bend as Proto
import ../src/lsp/path.bend as Path
import ../src/lsp/files/service.bend as Fs
import ../src/syntax/bind.bend as Bind
import ../src/syntax/outline.bend as Outline
import ../src/syntax/word.bend as Word
import ../laws/LspNavigationUsesBinder.bend as Laws
import ./lemmas/BoolEmptiness.bend as M1

# navigation
# ----------

# Unit for no text, Empty for one
def nav.none_ty(mm: Maybe<&2, String>) -> Type:
  match mm:
    case None{}:
      Unit
    case Some{_t}:
      Empty

# no text is some text
law nav.none_some:
  for -t: String
  for e: {None{} == Some{t} : Maybe<&2, String>}
  Empty

def nav.none_some(_t, e):
  %e : nav.none_ty(_)
  Unit{}

# a document the store holds is read from the store, not the files
law nav.miss_open:
  for -fs: Fs.Files
  for mm: Maybe<&2, String>
  for +text: String
  for h: {mm == Some{text} : Maybe<&2, String>}
  for path: String
  for -R: Type
  for -k: String -> IO.OP<R>
  {Nav.load.miss(~fs, mm, path, R, k) == k(text) : IO.OP<R>}

def nav.miss_open(fs, mm, text, h, path, R, k):
  match mm:
    case None{}:
      Empty.absurd({Nav.load.miss(~fs, None{}, path, R, k) == k(text) : IO.OP<R>}, nav.none_some(text, h))
    case Some{t}:
      Equal.cong(Maybe<&2, String>, IO.OP<R>, m => k(Maybe.default(&2, String, m, "")), Some{t}, Some{text}, h)

def Laws.nav_open_text(fs, docs, uri, text, h, R, k):
  nav.miss_open(fs, Docs.get(docs, uri), text, h, Proto.path(uri), R, k)

# the binder as the server wraps it is the binder as the law wraps it
law nav.here_local:
  for mm: Maybe<&2, Bind.Bind>
  for uri: String
  {Nav.here(mm, uri) == Laws.nav.local(mm, uri) : Maybe<&2, Nav.Found>}

def nav.here_local(mm, _uri):
  match mm:
    case None{}:
      {==}
    case Some{_b}:
      {==}

# definition on an open document is definition on its parsed text
law nav.open_at:
  for -fs: Fs.Files
  for +docs: List<&2, Docs.Doc>
  for +uri: String
  for +text: String
  for h: {Docs.get(docs, uri) == Some{text} : Maybe<&2, String>}
  for +line: U32
  for +col: U32
  for -R: Type
  for -k: Maybe<&2, Nav.Found> -> IO.OP<R>
  {Nav.at(~fs, docs, uri, line, col, R, k)
    == Nav.at.bound(~fs, Bind.bound(text), Outline.items(text), docs, uri, Word.at(text, line, col), line, col, R, k)
    : IO.OP<R>}

def nav.open_at(fs, docs, uri, text, h, line, col, R, k):
  h2 = Equal.sym(Maybe<&2, String>, Docs.get(docs, uri), Some{text}, h)
  %h2 : {Nav.load.miss(~fs, _, Proto.path(uri), R, tt => Nav.at.in(~fs, tt, docs, uri, line, col, R, k))
    == Nav.at.bound(~fs, Bind.bound(text), Outline.items(text), docs, uri, Word.at(text, line, col), line, col, R, k)
    : IO.OP<R>}
  {==}

# hover on an open document is hover on its parsed text
law nav.open_hover:
  for -fs: Fs.Files
  for +docs: List<&2, Docs.Doc>
  for +uri: String
  for +text: String
  for h: {Docs.get(docs, uri) == Some{text} : Maybe<&2, String>}
  for +line: U32
  for +col: U32
  for -R: Type
  for -k: Maybe<&2, Nav.Found> -> IO.OP<R>
  {Nav.hover(~fs, docs, uri, line, col, R, k)
    == Nav.hover.bound(~fs, Bind.bound(text), Outline.items(text), docs, uri, Word.at(text, line, col), line, col, R, k)
    : IO.OP<R>}

def nav.open_hover(fs, docs, uri, text, h, line, col, R, k):
  h2 = Equal.sym(Maybe<&2, String>, Docs.get(docs, uri), Some{text}, h)
  %h2 : {Nav.load.miss(~fs, _, Proto.path(uri), R, tt => Nav.hover.in(~fs, tt, docs, uri, line, col, R, k))
    == Nav.hover.bound(~fs, Bind.bound(text), Outline.items(text), docs, uri, Word.at(text, line, col), line, col, R, k)
    : IO.OP<R>}
  {==}

# definition over a parsed text answers the site the binder finds
law nav.bound_at:
  for -fs: Fs.Files
  for bb: Bind.Bound
  for +items: List<&2, Outline.Item>
  for +docs: List<&2, Docs.Doc>
  for +uri: String
  for +name: String
  for +line: U32
  for +col: U32
  for +site: Maybe<&2, Bind.Site>
  for hs: {Bind.at(bb, line, col) == site : Maybe<&2, Bind.Site>}
  for -R: Type
  for -k: Maybe<&2, Nav.Found> -> IO.OP<R>
  {Nav.at.bound(~fs, bb, items, docs, uri, name, line, col, R, k)
    == Nav.at.site(~fs, site, Laws.nav.binds(bb), items, docs, uri, name, R, k) : IO.OP<R>}

def nav.bound_at(fs, bb, items, docs, uri, name, line, col, site, hs, R, k):
  match bb:
    case Bind.Bound{+binds, uses, scopes}:
      hs2 = Equal.sym(Maybe<&2, Bind.Site>, Bind.at(Bind.Bound{binds, uses, scopes}, line, col), site, hs)
      %hs2 : {Nav.at.site(~fs, _, binds, items, docs, uri, name, R, k)
        == Nav.at.site(~fs, site, binds, items, docs, uri, name, R, k) : IO.OP<R>}
      {==}

# hover over a parsed text, at a use, answers what definition answers there
law nav.hover_bound_at:
  for -fs: Fs.Files
  for bb: Bind.Bound
  for +items: List<&2, Outline.Item>
  for +docs: List<&2, Docs.Doc>
  for +uri: String
  for +name: String
  for +line: U32
  for +col: U32
  for +u: Bind.Use
  for hs: {Bind.at(bb, line, col) == Some{Bind.SUse{u}} : Maybe<&2, Bind.Site>}
  for -R: Type
  for -k: Maybe<&2, Nav.Found> -> IO.OP<R>
  {Nav.hover.bound(~fs, bb, items, docs, uri, name, line, col, R, k)
    == Nav.at.site(~fs, Some{Bind.SUse{u}}, Laws.nav.binds(bb), items, docs, uri, name, R, k) : IO.OP<R>}

def nav.hover_bound_at(fs, bb, items, docs, uri, name, line, col, u, hs, R, k):
  match bb:
    case Bind.Bound{+binds, uses, scopes}:
      hs2 = Equal.sym(Maybe<&2, Bind.Site>, Bind.at(Bind.Bound{binds, uses, scopes}, line, col), Some{Bind.SUse{u}}, hs)
      %hs2 : {Nav.hover.site(~fs, _, items, binds, docs, uri, name, R, k)
        == Nav.at.site(~fs, Some{Bind.SUse{u}}, binds, items, docs, uri, name, R, k) : IO.OP<R>}
      {==}

# definition over an open text is what at.site answers for the site the
# binder finds there
law nav.open_site:
  for -fs: Fs.Files
  for +docs: List<&2, Docs.Doc>
  for +uri: String
  for +text: String
  for h: {Docs.get(docs, uri) == Some{text} : Maybe<&2, String>}
  for +line: U32
  for +col: U32
  for +site: Maybe<&2, Bind.Site>
  for hs: {Bind.at(Bind.bound(text), line, col) == site : Maybe<&2, Bind.Site>}
  for -R: Type
  for -k: Maybe<&2, Nav.Found> -> IO.OP<R>
  {Nav.at(~fs, docs, uri, line, col, R, k)
    == Nav.at.site(~fs, site, Laws.nav.binds(Bind.bound(text)), Outline.items(text), docs, uri,
      Word.at(text, line, col), R, k) : IO.OP<R>}

def nav.open_site(fs, docs, uri, text, h, line, col, site, hs, R, k):
  Equal.trans(IO.OP<R>, Nav.at(~fs, docs, uri, line, col, R, k),
    Nav.at.bound(~fs, Bind.bound(text), Outline.items(text), docs, uri, Word.at(text, line, col), line, col, R, k),
    Nav.at.site(~fs, site, Laws.nav.binds(Bind.bound(text)), Outline.items(text), docs, uri, Word.at(text, line, col),
      R, k),
    nav.open_at(fs, docs, uri, text, h, line, col, R, k),
    nav.bound_at(fs, Bind.bound(text), Outline.items(text), docs, uri, Word.at(text, line, col), line, col, site, hs,
      R, k))

def Laws.nav_definition_binder(fs, docs, uri, text, h, line, col, b, hs, R, k):
  nav.open_site(fs, docs, uri, text, h, line, col, Some{Bind.SBind{b}}, hs, R, k)

def Laws.nav_definition_local(fs, docs, uri, text, h, line, col, n, l, c, tl, tc, hs, R, k):
  Equal.trans(IO.OP<R>, Nav.at(~fs, docs, uri, line, col, R, k),
    k(Nav.here(Bind.binder(Laws.nav.binds(Bind.bound(text)), tl, tc), uri)),
    k(Laws.nav.local(Bind.binder(Laws.nav.binds(Bind.bound(text)), tl, tc), uri)),
    nav.open_site(fs, docs, uri, text, h, line, col, Some{Bind.SUse{Bind.Use{n, l, c, Bind.TLocal{tl, tc}}}}, hs, R, k),
    Equal.cong(Maybe<&2, Nav.Found>, IO.OP<R>, k, Nav.here(Bind.binder(Laws.nav.binds(Bind.bound(text)), tl, tc), uri),
      Laws.nav.local(Bind.binder(Laws.nav.binds(Bind.bound(text)), tl, tc), uri),
      nav.here_local(Bind.binder(Laws.nav.binds(Bind.bound(text)), tl, tc), uri)))

# an item of the document is answered as that item
law nav.own_some:
  for -fs: Fs.Files
  for +mm: Maybe<&2, Outline.Item>
  for +it: Outline.Item
  for hi: {mm == Some{it} : Maybe<&2, Outline.Item>}
  for +docs: List<&2, Docs.Doc>
  for +uri: String
  for +name: String
  for -R: Type
  for -k: Maybe<&2, Nav.Found> -> IO.OP<R>
  {Nav.own(~fs, mm, docs, uri, name, R, k) == k(Some{Nav.Found{uri, it}}) : IO.OP<R>}

def nav.own_some(fs, mm, it, hi, docs, uri, name, R, k):
  hi2 = Equal.sym(Maybe<&2, Outline.Item>, mm, Some{it}, hi)
  %hi2 : {Nav.own(~fs, _, docs, uri, name, R, k) == k(Some{Nav.Found{uri, it}}) : IO.OP<R>}
  {==}

def Laws.nav_definition_item(fs, docs, uri, text, h, line, col, n, l, c, item, hs, it, hi, R, k):
  Equal.trans(IO.OP<R>, Nav.at(~fs, docs, uri, line, col, R, k),
    Nav.own(~fs, Outline.find(Outline.items(text), item), docs, uri, item, R, k),
    k(Some{Nav.Found{uri, it}}),
    nav.open_site(fs, docs, uri, text, h, line, col, Some{Bind.SUse{Bind.Use{n, l, c, Bind.TItem{item}}}}, hs, R, k),
    nav.own_some(fs, Outline.find(Outline.items(text), item), it, hi, docs, uri, item, R, k))

# a name behind an import the outline has is looked up in the file it names
law nav.qual_some:
  for -fs: Fs.Files
  for +imp: Maybe<&2, String>
  for +rel: String
  for hi: {imp == Some{rel} : Maybe<&2, String>}
  for +rest: String
  for +items: List<&2, Outline.Item>
  for +docs: List<&2, Docs.Doc>
  for +uri: String
  for +name: String
  for -R: Type
  for -k: Maybe<&2, Nav.Found> -> IO.OP<R>
  {Nav.at.qual(~fs, imp, rest, items, docs, uri, name, R, k)
    == Nav.in_file(~fs, docs, Path.join(Path.dir(Proto.path(uri)), rel), rest, R, k) : IO.OP<R>}

def nav.qual_some(fs, imp, rel, hi, rest, items, docs, uri, name, R, k):
  hi2 = Equal.sym(Maybe<&2, String>, imp, Some{rel}, hi)
  %hi2 : {Nav.at.qual(~fs, _, rest, items, docs, uri, name, R, k)
    == Nav.in_file(~fs, docs, Path.join(Path.dir(Proto.path(uri)), rel), rest, R, k) : IO.OP<R>}
  {==}

def Laws.nav_definition_import(fs, docs, uri, text, h, line, col, n, l, c, alias, rest, hs, rel, hi, R, k):
  Equal.trans(IO.OP<R>, Nav.at(~fs, docs, uri, line, col, R, k),
    Nav.at.qual(~fs, Outline.import_path(Outline.items(text), alias), rest, Outline.items(text), docs, uri, n, R, k),
    Nav.in_file(~fs, docs, Path.join(Path.dir(Proto.path(uri)), rel), rest, R, k),
    nav.open_site(fs, docs, uri, text, h, line, col, Some{Bind.SUse{Bind.Use{n, l, c, Bind.TQual{alias, rest}}}}, hs,
      R, k),
    nav.qual_some(fs, Outline.import_path(Outline.items(text), alias), rel, hi, rest, Outline.items(text), docs, uri, n,
      R, k))

# a name the document has no item of is looked up in Base
law nav.own_none:
  for -fs: Fs.Files
  for +mm: Maybe<&2, Outline.Item>
  for hi: {mm == None{} : Maybe<&2, Outline.Item>}
  for +docs: List<&2, Docs.Doc>
  for +uri: String
  for +name: String
  for -R: Type
  for -k: Maybe<&2, Nav.Found> -> IO.OP<R>
  {Nav.own(~fs, mm, docs, uri, name, R, k) == Nav.in_base(~fs, docs, name, R, k) : IO.OP<R>}

def nav.own_none(fs, mm, hi, docs, uri, name, R, k):
  hi2 = Equal.sym(Maybe<&2, Outline.Item>, mm, None{}, hi)
  %hi2 : {Nav.own(~fs, _, docs, uri, name, R, k) == Nav.in_base(~fs, docs, name, R, k) : IO.OP<R>}
  {==}

def Laws.nav_definition_free(fs, docs, uri, text, h, line, col, n, l, c, hs, hi, R, k):
  Equal.trans(IO.OP<R>, Nav.at(~fs, docs, uri, line, col, R, k),
    Nav.own(~fs, Outline.find(Outline.items(text), n), docs, uri, n, R, k),
    Nav.in_base(~fs, docs, n, R, k),
    nav.open_site(fs, docs, uri, text, h, line, col, Some{Bind.SUse{Bind.Use{n, l, c, Bind.TFree{}}}}, hs, R, k),
    nav.own_none(fs, Outline.find(Outline.items(text), n), hi, docs, uri, n, R, k))

def Laws.nav_import_open(fs, docs, path, text, h, name, R, k):
  h2 = Equal.sym(Maybe<&2, String>, Docs.get(docs, "file://" ++ path), Some{text}, h)
  %h2 : {Nav.load.miss(~fs, _, path, R,
      tt => k(Nav.found(Outline.find(Outline.items(tt), name), "file://" ++ path)))
    == k(Nav.found(Outline.find(Outline.items(text), name), "file://" ++ path)) : IO.OP<R>}
  {==}

def Laws.nav_hover_use(fs, docs, uri, text, h, line, col, u, hs, R, k):
  +word = Word.at(text, line, col)
  Equal.trans(IO.OP<R>, Nav.hover(~fs, docs, uri, line, col, R, k),
    Nav.at.site(~fs, Some{Bind.SUse{u}}, Laws.nav.binds(Bind.bound(text)), Outline.items(text), docs, uri, word, R, k),
    Nav.at(~fs, docs, uri, line, col, R, k),
    Equal.trans(IO.OP<R>, Nav.hover(~fs, docs, uri, line, col, R, k),
      Nav.hover.bound(~fs, Bind.bound(text), Outline.items(text), docs, uri, word, line, col, R, k),
      Nav.at.site(~fs, Some{Bind.SUse{u}}, Laws.nav.binds(Bind.bound(text)), Outline.items(text), docs, uri, word,
        R, k),
      nav.open_hover(fs, docs, uri, text, h, line, col, R, k),
      nav.hover_bound_at(fs, Bind.bound(text), Outline.items(text), docs, uri, word, line, col, u, hs, R, k)),
    Equal.sym(IO.OP<R>, Nav.at(~fs, docs, uri, line, col, R, k),
      Nav.at.site(~fs, Some{Bind.SUse{u}}, Laws.nav.binds(Bind.bound(text)), Outline.items(text), docs, uri, word,
        R, k),
      nav.open_site(fs, docs, uri, text, h, line, col, Some{Bind.SUse{u}}, hs, R, k)))

# the server's positions for a site are the law's, whatever the site
law nav.sites_spec:
  for site: Maybe<&2, Bind.Site>
  for +bb: Bind.Bound
  {Nav.sites.of(site, bb) == Laws.nav.referenced(site, bb) : Nav.Sites}

def nav.sites_spec(site, _bb):
  match site:
    case None{}:
      {==}
    case Some{ss}:
      match ss:
        case Bind.SBind{b}:
          match b:
            case Bind.Bind{_name, _l, _c, kind, _note}:
              match kind:
                case Bind.KItem{}:
                  {==}
                case Bind.KCtor{}:
                  {==}
                case Bind.KParam{}:
                  {==}
                case Bind.KTypeParam{}:
                  {==}
                case Bind.KField{}:
                  {==}
                case Bind.KLocal{}:
                  {==}
                case Bind.KPat{}:
                  {==}
                case Bind.KFor{}:
                  {==}
                case Bind.KTypeVar{}:
                  {==}
        case Bind.SUse{u}:
          match u:
            case Bind.Use{_n, _l, _c, tg}:
              match tg:
                case Bind.TLocal{_tl, _tc}:
                  {==}
                case Bind.TItem{_item}:
                  {==}
                case Bind.TQual{_alias, _name}:
                  {==}
                case Bind.TFree{}:
                  {==}

def Laws.nav_references(fs, docs, uri, text, h, line, col, R, k):
  h2 = Equal.sym(Maybe<&2, String>, Docs.get(docs, uri), Some{text}, h)
  %h2 : {Nav.load.miss(~fs, _, Proto.path(uri), R, tt => k(Nav.sites.in(tt, line, col)))
    == k(Laws.nav.referenced(Bind.at(Bind.bound(text), line, col), Bind.bound(text))) : IO.OP<R>}
  Equal.cong(Nav.Sites, IO.OP<R>, k, Nav.sites.in(text, line, col),
    Laws.nav.referenced(Bind.at(Bind.bound(text), line, col), Bind.bound(text)),
    nav.sites_spec(Bind.at(Bind.bound(text), line, col), Bind.bound(text)))

def Laws.nav_completion(fs, docs, uri, text, h, prefix, line, hp, R, k):
  h2 = Equal.sym(Maybe<&2, String>, Docs.get(docs, uri), Some{text}, h)
  hp2 = Equal.sym(Maybe<&2, String>, Outline.import_path(Outline.items(text), Word.head(prefix)), None{}, hp)
  %h2 : {Nav.load.miss(~fs, _, Proto.path(uri), R, tt => Nav.candidates.in(~fs, tt, docs, uri, prefix, line, R, k))
    == Nav.from_base(~fs, Bool.not(String.is_empty(prefix)), docs, prefix, R,
      base => k(List.append(&2, Outline.Item, Laws.nav.locals(text, prefix, line), Laws.nav.after(text, prefix, base))))
    : IO.OP<R>}
  %hp2 : {Nav.candidates.via(~fs, _, Outline.items(text), docs, uri, prefix,
      Nav.as_items(Bind.visible(Bind.bound(text), line)), R, k)
    == Nav.from_base(~fs, Bool.not(String.is_empty(prefix)), docs, prefix, R,
      base => k(List.append(&2, Outline.Item, Laws.nav.locals(text, prefix, line), Laws.nav.after(text, prefix, base))))
    : IO.OP<R>}
  {==}

def Laws.nav_completion_import(fs, docs, uri, text, h, prefix, line, rel, hp, R, k):
  h2 = Equal.sym(Maybe<&2, String>, Docs.get(docs, uri), Some{text}, h)
  hp2 = Equal.sym(Maybe<&2, String>, Outline.import_path(Outline.items(text), Word.head(prefix)), Some{rel}, hp)
  %h2 : {Nav.load.miss(~fs, _, Proto.path(uri), R, tt => Nav.candidates.in(~fs, tt, docs, uri, prefix, line, R, k))
    == Nav.starting_in(~fs, docs, Path.join(Path.dir(Proto.path(uri)), rel), Word.rest(prefix),
        Word.head(prefix) ++ ".",
      R, k) : IO.OP<R>}
  %hp2 : {Nav.candidates.via(~fs, _, Outline.items(text), docs, uri, prefix,
      Nav.as_items(Bind.visible(Bind.bound(text), line)), R, k)
    == Nav.starting_in(~fs, docs, Path.join(Path.dir(Proto.path(uri)), rel), Word.rest(prefix),
        Word.head(prefix) ++ ".",
      R, k) : IO.OP<R>}
  {==}

# hover over a parsed text answers the site the binder finds
law nav.hover_bound_site:
  for -fs: Fs.Files
  for bb: Bind.Bound
  for +items: List<&2, Outline.Item>
  for +docs: List<&2, Docs.Doc>
  for +uri: String
  for +name: String
  for +line: U32
  for +col: U32
  for +site: Maybe<&2, Bind.Site>
  for hs: {Bind.at(bb, line, col) == site : Maybe<&2, Bind.Site>}
  for -R: Type
  for -k: Maybe<&2, Nav.Found> -> IO.OP<R>
  {Nav.hover.bound(~fs, bb, items, docs, uri, name, line, col, R, k)
    == Nav.hover.site(~fs, site, items, Laws.nav.binds(bb), docs, uri, name, R, k) : IO.OP<R>}

def nav.hover_bound_site(fs, bb, items, docs, uri, name, line, col, site, hs, R, k):
  match bb:
    case Bind.Bound{+binds, uses, scopes}:
      hs2 = Equal.sym(Maybe<&2, Bind.Site>, Bind.at(Bind.Bound{binds, uses, scopes}, line, col), site, hs)
      %hs2 : {Nav.hover.site(~fs, _, items, binds, docs, uri, name, R, k)
        == Nav.hover.site(~fs, site, items, binds, docs, uri, name, R, k) : IO.OP<R>}
      {==}

# hover over an open text is what hover.site answers for the site the
# binder finds there
law nav.open_hover_site:
  for -fs: Fs.Files
  for +docs: List<&2, Docs.Doc>
  for +uri: String
  for +text: String
  for h: {Docs.get(docs, uri) == Some{text} : Maybe<&2, String>}
  for +line: U32
  for +col: U32
  for +site: Maybe<&2, Bind.Site>
  for hs: {Bind.at(Bind.bound(text), line, col) == site : Maybe<&2, Bind.Site>}
  for -R: Type
  for -k: Maybe<&2, Nav.Found> -> IO.OP<R>
  {Nav.hover(~fs, docs, uri, line, col, R, k)
    == Nav.hover.site(~fs, site, Outline.items(text), Laws.nav.binds(Bind.bound(text)), docs, uri,
      Word.at(text, line, col), R, k) : IO.OP<R>}

def nav.open_hover_site(fs, docs, uri, text, h, line, col, site, hs, R, k):
  Equal.trans(IO.OP<R>, Nav.hover(~fs, docs, uri, line, col, R, k),
    Nav.hover.bound(~fs, Bind.bound(text), Outline.items(text), docs, uri, Word.at(text, line, col), line, col, R, k),
    Nav.hover.site(~fs, site, Outline.items(text), Laws.nav.binds(Bind.bound(text)), docs, uri,
      Word.at(text, line, col), R, k),
    nav.open_hover(fs, docs, uri, text, h, line, col, R, k),
    nav.hover_bound_site(fs, Bind.bound(text), Outline.items(text), docs, uri, Word.at(text, line, col), line, col,
      site, hs, R, k))

# a binder that names no item hovers as itself
law nav.kind_here:
  for -fs: Fs.Files
  for kind: Bind.BindKind
  for hk: {Laws.nav.item_kind(kind) == False{} : Bool}
  for +name: String
  for +items: List<&2, Outline.Item>
  for +docs: List<&2, Docs.Doc>
  for +uri: String
  for +bb: Bind.Bind
  for -R: Type
  for -k: Maybe<&2, Nav.Found> -> IO.OP<R>
  {Nav.hover.kind(~fs, kind, name, items, docs, uri, bb, R, k) == k(Some{Nav.Here{uri, bb}}) : IO.OP<R>}

def nav.kind_here(fs, kind, hk, name, items, docs, uri, bb, R, k):
  match kind:
    case Bind.KItem{}:
      Empty.absurd({Nav.hover.kind(~fs, Bind.KItem{}, name, items, docs, uri, bb, R, k) == k(Some{Nav.Here{uri, bb}})
        : IO.OP<R>}, M1.true_false(hk))
    case Bind.KCtor{}:
      {==}
    case Bind.KParam{}:
      {==}
    case Bind.KTypeParam{}:
      {==}
    case Bind.KField{}:
      {==}
    case Bind.KLocal{}:
      {==}
    case Bind.KPat{}:
      {==}
    case Bind.KFor{}:
      {==}
    case Bind.KTypeVar{}:
      {==}

def Laws.nav_hover_binder(fs, docs, uri, text, h, line, col, name, bl, bc, kind, note, hs, hk, R, k):
  Equal.trans(IO.OP<R>, Nav.hover(~fs, docs, uri, line, col, R, k),
    Nav.hover.site(~fs, Some{Bind.SBind{Bind.Bind{name, bl, bc, kind, note}}}, Outline.items(text),
      Laws.nav.binds(Bind.bound(text)), docs, uri, Word.at(text, line, col), R, k),
    k(Some{Nav.Here{uri, Bind.Bind{name, bl, bc, kind, note}}}),
    nav.open_hover_site(fs, docs, uri, text, h, line, col, Some{Bind.SBind{Bind.Bind{name, bl, bc, kind, note}}}, hs,
      R, k),
    nav.kind_here(fs, kind, hk, name, Outline.items(text), docs, uri, Bind.Bind{name, bl, bc, kind, note}, R, k))

# hover on an item's own name, behind an import the outline has
law nav.item_import:
  for -fs: Fs.Files
  for +docs: List<&2, Docs.Doc>
  for +uri: String
  for +text: String
  for h: {Docs.get(docs, uri) == Some{text} : Maybe<&2, String>}
  for +name: String
  for +bb: Bind.Bind
  for +rel: String
  for hi: {Outline.import_path(Outline.items(text), Word.head(name)) == Some{rel} : Maybe<&2, String>}
  for -R: Type
  for -k: Maybe<&2, Nav.Found> -> IO.OP<R>
  {Nav.hover.item(~fs, name, Outline.items(text), docs, uri, bb, R, k)
    == Nav.in_file(~fs, docs, Path.join(Path.dir(Proto.path(uri)), rel), Word.rest(name), R,
      mm => k(Nav.hover.pick(mm, Nav.found(Outline.find(Outline.items(text), name), uri), uri, bb))) : IO.OP<R>}

def nav.item_import(fs, docs, uri, text, h, name, bb, rel, hi, R, k):
  h2 = Equal.sym(Maybe<&2, String>, Docs.get(docs, uri), Some{text}, h)
  hi2 = Equal.sym(Maybe<&2, String>, Outline.import_path(Outline.items(text), Word.head(name)), Some{rel}, hi)
  %h2 : {Nav.load.miss(~fs, _, Proto.path(uri), R,
      tt => Nav.among(~fs, Outline.items(tt), docs, uri, name, R,
        mm => k(Nav.hover.pick(mm, Nav.found(Outline.find(Outline.items(text), name), uri), uri, bb))))
    == Nav.in_file(~fs, docs, Path.join(Path.dir(Proto.path(uri)), rel), Word.rest(name), R,
      mm => k(Nav.hover.pick(mm, Nav.found(Outline.find(Outline.items(text), name), uri), uri, bb))) : IO.OP<R>}
  %hi2 : {Nav.via(~fs, _, docs, uri, name, Outline.items(text), R,
      mm => k(Nav.hover.pick(mm, Nav.found(Outline.find(Outline.items(text), name), uri), uri, bb)))
    == Nav.in_file(~fs, docs, Path.join(Path.dir(Proto.path(uri)), rel), Word.rest(name), R,
      mm => k(Nav.hover.pick(mm, Nav.found(Outline.find(Outline.items(text), name), uri), uri, bb))) : IO.OP<R>}
  {==}

def Laws.nav_hover_item(fs, docs, uri, text, h, line, col, name, bl, bc, note, hs, rel, hi, R, k):
  Equal.trans(IO.OP<R>, Nav.hover(~fs, docs, uri, line, col, R, k),
    Nav.hover.site(~fs, Some{Bind.SBind{Bind.Bind{name, bl, bc, Bind.KItem{}, note}}}, Outline.items(text),
      Laws.nav.binds(Bind.bound(text)), docs, uri, Word.at(text, line, col), R, k),
    Nav.in_file(~fs, docs, Path.join(Path.dir(Proto.path(uri)), rel), Word.rest(name), R,
      mm => k(Nav.hover.pick(mm, Nav.found(Outline.find(Outline.items(text), name), uri), uri,
        Bind.Bind{name, bl, bc, Bind.KItem{}, note}))),
    nav.open_hover_site(fs, docs, uri, text, h, line, col,
      Some{Bind.SBind{Bind.Bind{name, bl, bc, Bind.KItem{}, note}}}, hs, R, k),
    nav.item_import(fs, docs, uri, text, h, name, Bind.Bind{name, bl, bc, Bind.KItem{}, note}, rel, hi, R, k))

# hover on an item's own name, under no import, found in the document
law nav.item_own:
  for -fs: Fs.Files
  for +docs: List<&2, Docs.Doc>
  for +uri: String
  for +text: String
  for h: {Docs.get(docs, uri) == Some{text} : Maybe<&2, String>}
  for +name: String
  for +bb: Bind.Bind
  for hi: {Outline.import_path(Outline.items(text), Word.head(name)) == None{} : Maybe<&2, String>}
  for +it: Outline.Item
  for hf: {Outline.find(Outline.items(text), name) == Some{it} : Maybe<&2, Outline.Item>}
  for -R: Type
  for -k: Maybe<&2, Nav.Found> -> IO.OP<R>
  {Nav.hover.item(~fs, name, Outline.items(text), docs, uri, bb, R, k) == k(Some{Nav.Found{uri, it}}) : IO.OP<R>}

def nav.item_own(fs, docs, uri, text, h, name, bb, hi, it, hf, R, k):
  h2 = Equal.sym(Maybe<&2, String>, Docs.get(docs, uri), Some{text}, h)
  hi2 = Equal.sym(Maybe<&2, String>, Outline.import_path(Outline.items(text), Word.head(name)), None{}, hi)
  hf2 = Equal.sym(Maybe<&2, Outline.Item>, Outline.find(Outline.items(text), name), Some{it}, hf)
  %h2 : {Nav.load.miss(~fs, _, Proto.path(uri), R,
      tt => Nav.among(~fs, Outline.items(tt), docs, uri, name, R,
        mm => k(Nav.hover.pick(mm, Nav.found(Outline.find(Outline.items(text), name), uri), uri, bb))))
    == k(Some{Nav.Found{uri, it}}) : IO.OP<R>}
  %hi2 : {Nav.via(~fs, _, docs, uri, name, Outline.items(text), R,
      mm => k(Nav.hover.pick(mm, Nav.found(Outline.find(Outline.items(text), name), uri), uri, bb)))
    == k(Some{Nav.Found{uri, it}}) : IO.OP<R>}
  %hf2 : {Nav.own(~fs, _, docs, uri, name, R,
      mm => k(Nav.hover.pick(mm, Nav.found(_, uri), uri, bb)))
    == k(Some{Nav.Found{uri, it}}) : IO.OP<R>}
  {==}

def Laws.nav_hover_own(fs, docs, uri, text, h, line, col, name, bl, bc, note, hs, hi, it, hf, R, k):
  Equal.trans(IO.OP<R>, Nav.hover(~fs, docs, uri, line, col, R, k),
    Nav.hover.site(~fs, Some{Bind.SBind{Bind.Bind{name, bl, bc, Bind.KItem{}, note}}}, Outline.items(text),
      Laws.nav.binds(Bind.bound(text)), docs, uri, Word.at(text, line, col), R, k),
    k(Some{Nav.Found{uri, it}}),
    nav.open_hover_site(fs, docs, uri, text, h, line, col,
      Some{Bind.SBind{Bind.Bind{name, bl, bc, Bind.KItem{}, note}}}, hs, R, k),
    nav.item_own(fs, docs, uri, text, h, name, Bind.Bind{name, bl, bc, Bind.KItem{}, note}, hi, it, hf, R, k))
