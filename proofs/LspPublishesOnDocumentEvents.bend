# proofs of laws/LspPublishesOnDocumentEvents.bend
import Base
import ../src/lazy/lazy.bend as Lazy
import ../src/lsp/docs.bend as Docs
import ../src/role.bend as Role
import ../src/src.bend as Src
import ../src/lsp/report.bend as Rep
import ../src/finding.bend as F
import ../src/config.bend as Config
import ../src/rules.bend as Rules
import ../src/lint/plan.bend as Plan
import ../src/noqa.bend as Noqa
import ../src/syntax/lex.bend as Lex
import ../laws/LspPublishesOnDocumentEvents.bend as Laws
import ./lemmas/PublishComparisons.bend as M1

# the document just put at the head of the list is the one a lookup of its
# URI finds: its errors
law pub.errors_head:
  for +uri: String
  for -text: String
  for -ds: List<&2, Rep.Diag>
  for -ms: List<&2, Role.Mark>
  for -rest: List<&2, Docs.Doc>
  {Docs.errors(Docs.Doc{uri, text, ds, ms} <> rest, uri) == ds : List<&2, Rep.Diag>}

def pub.errors_head(uri, _text, ds, _ms, rest):
  e = Equal.sym(Bool, String.eq(uri, uri), True{}, M1.pub.seq_refl(uri))
  %e : {Lazy.stop(List<&2, Rep.Diag>, _, ds, _u => Docs.errors(rest, uri)) == ds : List<&2, Rep.Diag>}
  {==}

# and its text
law pub.get_head:
  for +uri: String
  for -text: String
  for -ds: List<&2, Rep.Diag>
  for -ms: List<&2, Role.Mark>
  for -rest: List<&2, Docs.Doc>
  {Docs.get(Docs.Doc{uri, text, ds, ms} <> rest, uri) == Some{text} : Maybe<&2, String>}

def pub.get_head(uri, text, _ds, _ms, rest):
  e = Equal.sym(Bool, String.eq(uri, uri), True{}, M1.pub.seq_refl(uri))
  %e : {Lazy.stop(Maybe<&2, String>, _, Some{text}, _u => Docs.get(rest, uri)) == Some{text} : Maybe<&2, String>}
  {==}

# one document onto the rest, the URI's removed: none of its errors survive
law pub.del.step:
  for bb: Bool
  for +u: String
  for +uri: String
  for -t: String
  for -e: List<&2, Rep.Diag>
  for -m: List<&2, Role.Mark>
  for +rest: List<&2, Docs.Doc>
  for h: {String.eq(u, uri) == bb : Bool}
  for ih: {Docs.errors(rest, uri) == [] : List<&2, Rep.Diag>}
  {Docs.errors(Bool.pick(List<&2, Docs.Doc>, bb, rest, Docs.Doc{u, t, e, m} <> rest), uri) == []
    : List<&2, Rep.Diag>}

def pub.del.step(bb, u, uri, _t, e, _m, rest, h, ih):
  match bb:
    case True{}:
      ih
    case False{}:
      g = Equal.sym(Bool, String.eq(u, uri), False{}, h)
      %g : {Lazy.stop(List<&2, Rep.Diag>, _, e, _u => Docs.errors(rest, uri)) == [] : List<&2, Rep.Diag>}
      ih

# the documents without a URI hold no errors for it
law pub.del:
  for docs: List<&2, Docs.Doc>
  for +uri: String
  {Docs.errors(Docs.del(docs, uri), uri) == [] : List<&2, Rep.Diag>}

def pub.del(docs, uri):
  match docs:
    case Nil{}:
      {==}
    case Con{Docs.Doc{+u, t, e, m}, +r}:
      pub.del.step(String.eq(u, uri), u, uri, t, e, m, Docs.del(r, uri), {==}, pub.del(r, uri))

def Laws.open_publishes(_ee, _uri, _text, _ds, _rs, _ms, _docs):
  {==}

def Laws.save_publishes(_ee, _uri, _ds, _rs, _ms, _docs):
  {==}

def Laws.change_publishes(_ee, _uri, _text, _rs, _docs):
  {==}

def Laws.open_keeps(_ee, uri, text, ds, _rs, ms, docs):
  (pub.errors_head(uri, Maybe.default(&2, String, Docs.get(Docs.set(docs, uri, text), uri), ""), ds, ms,
      Docs.del(Docs.set(docs, uri, text), uri)),
    Equal.trans(Maybe<&2, String>,
      Docs.get(Docs.set_checked(Docs.set(docs, uri, text), uri, ds, ms), uri),
      Some{Maybe.default(&2, String, Docs.get(Docs.set(docs, uri, text), uri), "")}, Some{text},
      pub.get_head(uri, Maybe.default(&2, String, Docs.get(Docs.set(docs, uri, text), uri), ""), ds, ms,
        Docs.del(Docs.set(docs, uri, text), uri)),
      Equal.cong(Maybe<&2, String>, Maybe<&2, String>, m => Some{Maybe.default(&2, String, m, "")},
        Docs.get(Docs.set(docs, uri, text), uri), Some{text},
        pub.get_head(uri, text, Docs.errors(docs, uri), Docs.marks(docs, uri), Docs.del(docs, uri)))))

def Laws.save_keeps(_ee, uri, ds, _rs, ms, docs):
  pub.errors_head(uri, Maybe.default(&2, String, Docs.get(docs, uri), ""), ds, ms, Docs.del(docs, uri))

def Laws.change_keeps(_ee, uri, text, _rs, docs):
  (pub.errors_head(uri, text, Docs.errors(docs, uri), Docs.marks(docs, uri), Docs.del(docs, uri)),
    pub.get_head(uri, text, Docs.errors(docs, uri), Docs.marks(docs, uri), Docs.del(docs, uri)))

def Laws.close_publishes(_ee, uri, docs):
  ({==}, pub.del(docs, uri))

def Laws.config_unlinted(path, h, _text, _rs, _ms):
  e = Equal.sym(Bool, Plan.is_config(path), True{}, h)
  %e : {Bool.pick(List<&2, F.Graded>, _, [],
      Plan.after([Noqa.file(path, Lex.tokens(_text))], False{},
        Rules.graded(Config.nearest(_rs), Rules.on.role(Config.nearest(_rs), Role.of(_ms, path), Src.of(path, _text))),
        fs => Rules.graded(Config.nearest(_rs), fs)))
    == [] : List<&2, F.Graded>}
  {==}
