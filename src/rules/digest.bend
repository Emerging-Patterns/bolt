# src/rules/digest: one small reading of each file for the project rules.
# A project rule sees every file at once, and a `+` reuse of that list copies
# it: handed the parsed `Src` (src/src.bend), each extra use duplicated every
# file's text, tokens and tree, and the pair of project rules grew faster than
# the file count (100 files cost 362 s that way). So each file is read down
# once to what those rules ask of it -- its path, its top-level defs and types
# by name and line, what its laws name, what it imports, and its laws -- and
# the phases run over these, which are strings and cheap to copy.
import Base
import ../src.bend as Src
import ../syntax/lex.bend as Lex
import ../syntax/tree.bend as Tree
import ../syntax/bind.bend as Bind
import ../syntax/outline.bend as Outline
import ../lazy/lazy.bend as Lazy
import ./imports.bend as Imports
import ./laws/closed.bend as Closed
import ../paths.bend as Paths
import ../role.bend as Role
import ./calls.bend as Calls

# what a file holds
# -----------------

# a law names an item of a module: its path and its name
type Mention is Data:
  Mention{path: String, name: String}

# a top-level def or type, by kind, name and the line it starts on, with a
# type's constructors by name (none for a def), and what the uses on its
# lines name (its calls, for a def): each as the binder resolved it, an item
# of the file or one behind an import alias
type Top is Data:
  Top{kind: Outline.ItemKind, name: String, line: U32, ctors: List<&2, String>, calls: List<&2, Mention>}

# a law of a LAWS.bend: its name, the line it starts on, whether it binds
# (a `for` or `exs` line), and the lines of its comment block, `# ` dropped
type Law is Data:
  Law{name: String, line: U32, binds: Bool, doc: List<&2, String>}

# one file as the project rules see it: its path as given and normalized, its
# directory, whether it states laws (LAWS.bend) or proves them too
# (PROOF.bend), whether the coverage rule lets it off, its top-level items, what
# its own laws name, the files it imports, and its laws
type Digest is Data:
  Digest{path: String, norm: String, dir: String, is_laws: Bool, is_law_file: Bool, exempt: Bool,
    tops: List<&2, Top>, says: List<&2, Mention>, deps: List<&2, String>,
    laws: List<&2, Law>}

# what the laws name
# ------------------

# an import alias and the path it names
type Alias is Data:
  Alias{name: String, path: String}

# the aliases a file imports
def aliases(items: List<&2, Outline.Item>, +from: String) -> List<&2, Alias>:
  match items:
    case Nil{}:
      Nil{}
    case Con{Outline.Item{Outline.IImport{}, name, line, sig, doc, path}, rest}:
      Alias{name, Imports.resolve(from, path)} <> aliases(rest, from)
    case Con{other, rest}:
      aliases(rest, from)

# the path an alias names, when it is one; hit: the alias before as was
# the name, so the search stops there
def alias_path.go(as: List<&2, Alias>, +name: String, hit: Maybe<&2, String>) -> Maybe<&2, String>:
  match as:
    case Nil{}:
      hit
    case Con{Alias{+n, p}, rest}:
      match hit:
        case Some{x}:
          Some{x}
        case None{}:
          alias_path.go(rest, name, Bool.pick(Maybe<&2, String>, String.eq(n, name), Some{p}, None{}))

# the path an alias names, when it is one: the first alias of the name
def alias_path(as: List<&2, Alias>, +name: String) -> Maybe<&2, String>:
  alias_path.go(as, name, None{})

# the lines a quantified law's statement spans: from its header's first token
# to its body's last
type Span is Data:
  Span{from: U32, upto: U32}

# the spans of every quantified law of a tree, in order. A closed law spans
# nothing (it covers one input, not the def)
def spans(root: Tree.Node) -> List<&2, Span>:
  match root:
    case Tree.NCons{Tree.Stmt{Tree.SLaw{}, kids, +body}, rest}:
      +more = spans(rest)
      Bool.pick(List<&2, Span>, Closed.binds(body),
        Span{Tree.line(kids), Tree.line.of(List.head(&2, Lex.Tok, Tree.leaves.go(body, [])))} <> more, more)
    case Tree.NCons{h, rest}:
      spans(rest)
    case other:
      Nil{}

# is the line in one of the spans?
def within(s: List<&2, Span>, +ln: U32) -> Bool:
  match s:
    case Nil{}:
      False{}
    case Con{Span{+from, +upto}, rest}:
      Lazy.or_else(Bool.and(U32.is_le(from, ln), U32.is_le(ln, upto)), _u => within(rest, ln))

# an item behind an alias, when an import names the alias, onto the others
def aliased(m: Maybe<&2, String>, +name: String, more: List<&2, Mention>) -> List<&2, Mention>:
  match m:
    case Some{p}:
      Mention{p, name} <> more
    case None{}:
      more

# what the binder resolved a use to, as a mention onto the others: an item of
# the law's own file, or an item of the file an import alias names; nothing
# for a binder, a free name, or an alias no import names
def target(t: Bind.Target, +as: List<&2, Alias>, +file: String, more: List<&2, Mention>) -> List<&2, Mention>:
  match t:
    case Bind.TItem{n}:
      Mention{file, n} <> more
    case Bind.TQual{a, n}:
      aliased(alias_path(as, a), n, more)
    case other:
      more

# the mentions of every use the binder records in the statement of a
# quantified law, in order. Its header's own name is a binder, not a use
def mentions(us: List<&2, Bind.Use>, +s: List<&2, Span>, +as: List<&2, Alias>, +file: String) -> List<&2, Mention>:
  match us:
    case Nil{}:
      Nil{}
    case Con{Bind.Use{n, +l, c, t}, rest}:
      +more = mentions(rest, s, as, file)
      +out = Bool.not(within(s, l))
      Lazy.stop(List<&2, Mention>, out, more, _u => target(t, as, file, more))

# the uses the binder recorded
def uses.of(b: Bind.Bound) -> List<&2, Bind.Use>:
  match b:
    case Bind.Bound{bs, us, scs}:
      us

# what the file holds besides
# ---------------------------

# the names of the constructors the items open with: a type's, since the
# outline lists them right after it
def ctors(items: List<&2, Outline.Item>) -> List<&2, String>:
  match items:
    case Con{Outline.Item{Outline.ICtor{}, name, line, sig, doc, path}, rest}:
      name <> ctors(rest)
    case other:
      Nil{}

# the uses, in order, before the first one at or past the line
def before(us: List<&2, Bind.Use>, +at: U32) -> List<&2, Bind.Use>:
  match us:
    case Nil{}:
      Nil{}
    case Con{Bind.Use{nm, +l, c, t}, rest}:
      Lazy.stop(List<&2, Bind.Use>, U32.is_le(at, l), [], _u => Bind.Use{nm, l, c, t} <> before(rest, at))

# the uses from the first one at or past the line on
def after(us: List<&2, Bind.Use>, +at: U32) -> List<&2, Bind.Use>:
  match us:
    case Nil{}:
      Nil{}
    case Con{Bind.Use{nm, +l, c, t}, +rest}:
      Lazy.stop(List<&2, Bind.Use>, U32.is_le(at, l), Bind.Use{nm, l, c, t} <> rest, _u => after(rest, at))

# the uses before the line, when there is one; else all of them
def upto(us: List<&2, Bind.Use>, m: Maybe<&2, U32>) -> List<&2, Bind.Use>:
  match m:
    case None{}:
      us
    case Some{at}:
      before(us, at)

# the uses from the line on, when there is one; else none
def past(us: List<&2, Bind.Use>, m: Maybe<&2, U32>) -> List<&2, Bind.Use>:
  match m:
    case None{}:
      Nil{}
    case Some{at}:
      after(us, at)

# the line of the next item that ends an item's lines: any but a constructor,
# which the outline lists inside its type
def next_line(items: List<&2, Outline.Item>) -> Maybe<&2, U32>:
  match items:
    case Nil{}:
      None{}
    case Con{Outline.Item{Outline.ICtor{}, name, line, sig, doc, path}, rest}:
      next_line(rest)
    case Con{Outline.Item{kind, name, line, sig, doc, path}, rest}:
      Some{line}

# what the uses name, in order: an item of the file, or one behind an alias
def called(us: List<&2, Bind.Use>, +as: List<&2, Alias>, +file: String) -> List<&2, Mention>:
  match us:
    case Nil{}:
      Nil{}
    case Con{Bind.Use{n, l, c, t}, rest}:
      target(t, as, file, called(rest, as, file))

# the names of the top-level defs that are proofs (Calls.proof: one that
# returns a proof, or one written with no type, which is how Bend fills the
# law named f). The law states their property, so the coverage rule neither
# grades them nor walks through them
def proofs(ds: List<&2, Calls.Def>) -> List<&2, String>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{Calls.Def{name, +sig, body}, rest}:
      +more = proofs(rest)
      Bool.pick(List<&2, String>, Calls.proof(sig), name <> more, more)

# ranged, asking the list of the proofs' names where ranged asks their index:
# the walk the laws are proved on (proofs/LawNamesEveryItem.bend shows the two
# equal). The top-level defs and types, by name and line, less the defs that
# are proofs (ps): what the coverage rule grades. The uses are read in order,
# once: each item but a constructor takes those before the next such item's
# line, and a def or a type keeps what they name (a def's calls)
def ranged.spec(
  items: List<&2, Outline.Item>,
  +us: List<&2, Bind.Use>,
  +as: List<&2, Alias>,
  +file: String,
  +ps: List<&2, String>
) -> List<&2, Top>:
  match items:
    case Nil{}:
      Nil{}
    case Con{Outline.Item{Outline.ICtor{}, name, line, sig, doc, path}, rest}:
      ranged.spec(rest, us, as, file, ps)
    case Con{Outline.Item{Outline.IDef{}, +name, line, sig, doc, path}, +rest}:
      +nx = next_line(rest)
      cs = called(upto(us, nx), as, file)
      +more = ranged.spec(rest, past(us, nx), as, file, ps)
      Bool.pick(List<&2, Top>, Imports.has(ps, name), more, Top{Outline.IDef{}, name, line, [], cs} <> more)
    case Con{Outline.Item{Outline.IType{}, name, line, sig, doc, path}, +rest}:
      +nx = next_line(rest)
      Top{Outline.IType{}, name, line, ctors(rest), called(upto(us, nx), as, file)}
        <> ranged.spec(rest, past(us, nx), as, file, ps)
    case Con{Outline.Item{kind, name, line, sig, doc, path}, +rest}:
      ranged.spec(rest, past(us, next_line(rest)), as, file, ps)

# the top-level defs and types, by name and line, less the defs that are
# proofs (px, the index of their names: a scan of the names for each def is
# the defs times the proofs, 18 s on a generated file of 21,344 untyped defs
# and 0.2 s through the index): what the coverage rule grades. The uses are
# read in order, once: each item but a constructor takes those before the
# next such item's line, and a def or a type keeps what they name (a def's
# calls)
def ranged(
  items: List<&2, Outline.Item>,
  +us: List<&2, Bind.Use>,
  +as: List<&2, Alias>,
  +file: String,
  +px: Bind.Index
) -> List<&2, Top>:
  match items:
    case Nil{}:
      Nil{}
    case Con{Outline.Item{Outline.ICtor{}, name, line, sig, doc, path}, rest}:
      ranged(rest, us, as, file, px)
    case Con{Outline.Item{Outline.IDef{}, +name, line, sig, doc, path}, +rest}:
      +nx = next_line(rest)
      cs = called(upto(us, nx), as, file)
      +more = ranged(rest, past(us, nx), as, file, px)
      Bool.pick(List<&2, Top>, Bind.indexed(px, name), more, Top{Outline.IDef{}, name, line, [], cs} <> more)
    case Con{Outline.Item{Outline.IType{}, name, line, sig, doc, path}, +rest}:
      +nx = next_line(rest)
      Top{Outline.IType{}, name, line, ctors(rest), called(upto(us, nx), as, file)}
        <> ranged(rest, past(us, nx), as, file, px)
    case Con{Outline.Item{kind, name, line, sig, doc, path}, +rest}:
      ranged(rest, past(us, next_line(rest)), as, file, px)

# a law file or a test, by its path alone: not under law. Nothing the file's
# text mentions exempts it; IO is not an exemption, since an IO equality is a
# law.
def is_exempt(+p: String) -> Bool:
  Bool.or(Paths.is_law_file(p), Paths.is_test(p))

# the laws
# --------

# the doc of the item on a line; the items are in line order, so the search
# stops at it
def doc_at(items: List<&2, Outline.Item>, +at: U32) -> String:
  match items:
    case Nil{}:
      ""
    case Con{Outline.Item{k, n, +ln, sig, +doc, p}, rest}:
      Lazy.stop(String, U32.is_le(at, ln), Bool.pick(String, U32.is_eq(ln, at), doc, ""), _u => doc_at(rest, at))

# does the first item sit on or after a line (from_line stops there)?
def from_line.stop(items: List<&2, Outline.Item>, +at: U32) -> Bool:
  match items:
    case Nil{}:
      True{}
    case Con{Outline.Item{k, n, +ln, sig, doc, p}, rest}:
      U32.is_le(at, ln)

# the items from the first on or after a line; the items are in line order,
# and so are a tree's laws, so an item this drops lies above every later law
# too. stop is from_line.stop of items, carried so the step stays a loop
def from_line(items: List<&2, Outline.Item>, +at: U32, +stop: Bool) -> List<&2, Outline.Item>:
  match items:
    case Nil{}:
      Nil{}
    case Con{h, +rest}:
      match stop:
        case True{}:
          h <> rest
        case False{}:
          from_line(rest, at, from_line.stop(rest, at))

# every law of a tree, with whether it binds and its doc lines. items is a
# cursor: each law's search starts where the last one stopped, so the items
# are read once over all the laws, not once per law
def laws_of(root: Tree.Node, +items: List<&2, Outline.Item>) -> List<&2, Law>:
  match root:
    case Tree.NCons{Tree.Stmt{Tree.SLaw{}, +kids, body}, rest}:
      +at = Tree.line(kids)
      +left = from_line(items, at, from_line.stop(items, at))
      d = doc_at(left, at)
      Law{Closed.name.of(Bind.declared(kids)), at, Closed.binds(body), String.lines(d)} <> laws_of(rest, left)
    case Tree.NCons{h, rest}:
      laws_of(rest, items)
    case other:
      Nil{}

# the laws of a LAWS.bend; no other file states any
def laws.in(is_laws: Bool, root: Tree.Node, items: List<&2, Outline.Item>) -> List<&2, Law>:
  match is_laws:
    case True{}:
      laws_of(root, items)
    case False{}:
      Nil{}

# the digest
# ----------

# what a file's laws name: only a LAWS.bend states laws that cover a def
def stated(is_laws: Bool, root: Tree.Node, bound: Bind.Bound, as: List<&2, Alias>, file: String) -> List<&2, Mention>:
  match is_laws:
    case True{}:
      mentions(uses.of(bound), spans(root), as, file)
    case False{}:
      Nil{}

# one parsed file read down to its digest
def of(s2: Src.Src) -> Digest:
  Src.Src{+path, text, toks, +tree, +bound, +items} = s2
  +p = Imports.norm(path)
  +as = aliases(items, p)
  Digest{path, p, Imports.dir_of(path), Paths.is_laws(path), Paths.is_law_file(path), is_exempt(p),
    ranged(items, uses.of(bound), as, p, Bind.index(proofs(Calls.defs(tree)))),
    stated(Paths.is_laws(path), tree, bound, as, p),
    Imports.targets(items, p),
    laws.in(Paths.is_laws(path), tree, items)}

# one parsed file read down to its digest, told its role (src/role.bend): a
# law file states the laws that cover defs, and a law or proof file is exempt
def of.role(+r: Role.Role, s2: Src.Src) -> Digest:
  Src.Src{+path, text, toks, +tree, +bound, +items} = s2
  +p = Imports.norm(path)
  +as = aliases(items, p)
  +laws = Role.is_laws(r)
  Digest{path, p, Imports.dir_of(path), laws, Role.is_law_file(r), Bool.or(Role.is_law_file(r), Paths.is_test(p)),
    ranged(items, uses.of(bound), as, p, Bind.index(proofs(Calls.defs(tree)))),
    stated(laws, tree, bound, as, p),
    Imports.targets(items, p),
    laws.in(laws, tree, items)}

# one parsed file's digest, told its role among the marks (src/role.bend)
def of.marked(+ms: List<&2, Role.Mark>, s2: Src.Src) -> Digest:
  Src.Src{+path, text, toks, tree, bound, items} = s2
  of.role(Role.of(ms, path), Src.Src{path, text, toks, tree, bound, items})

# every file the linter read, each with its role among the marks, in one
# pass, in order
def all.role(+ms: List<&2, Role.Mark>, ss: List<&2, Src.Src>) -> List<&2, Digest>:
  match ss:
    case Nil{}:
      Nil{}
    case Con{s, rest}:
      of.marked(ms, s) <> all.role(ms, rest)

# the import graph of the files, built once for every closure taken over it
def edges(ds: List<&2, Digest>) -> List<&2, Imports.Edge>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{Digest{path, norm, dir, is_laws, is_law_file, exempt, tops, says, deps, laws}, rest}:
      Imports.Edge{norm, deps} <> edges(rest)
