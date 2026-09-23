# bolt/rules/digest: one small reading of each file for the project rules.
# A project rule sees every file at once, and a `+` reuse of that list copies
# it: handed the parsed `Src` (bolt/src.bend), each extra use duplicated every
# file's text, tokens and tree, and the pair of project rules grew faster than
# the file count (100 files cost 362 s that way). So each file is read down
# once to what those rules ask of it -- its path, its top-level defs and types
# by name and line, what its laws name, what it imports, and its `@unsafe`
# defs -- and the phases run over these, which are strings and cheap to copy.
import Base
import ../src.bend as Src
import ../../syntax/lex.bend as Lex
import ../../syntax/tree.bend as Tree
import ../../syntax/bind.bend as Bind
import ../../syntax/outline.bend as Outline
import ../../lazy/lazy.bend as Lazy
import ./imports.bend as Imports
import ./laws/closed.bend as Closed
import ../paths.bend as Paths

# what a file holds
# -----------------

# a law names an item of a module: its path and its name
type Mention is Data:
  Mention{path: String, name: String}

# a top-level def or type, by kind, name and the line it starts on, with a
# type's constructors by name (none for a def)
type Top is Data:
  Top{kind: Outline.ItemKind, name: String, line: U32, ctors: List<&2, String>}

# an `@unsafe def` and where its `@` is
type Unsafe is Data:
  Unsafe{name: String, line: U32, col: U32}

# a law of a LAWS.bend: its name, the line it starts on, whether it binds
# (a `for` or `exs` line), and the lines of its comment block, `# ` dropped
type Law is Data:
  Law{name: String, line: U32, binds: Bool, doc: List<&2, String>}

# one file as the project rules see it: its path as given and normalized, its
# directory, whether it states laws (LAWS.bend) or proves them too
# (PROOF.bend), whether the coverage rule lets it off, its top-level items, what
# its own laws name, the files it imports, and its `@unsafe` defs
type Digest is Data:
  Digest{path: String, norm: String, dir: String, is_laws: Bool, is_law_file: Bool, exempt: Bool,
    tops: List<&2, Top>, says: List<&2, Mention>, deps: List<&2, String>, unsafes: List<&2, Unsafe>,
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

# the path an alias names, when it is one
def alias_path(as: List<&2, Alias>, +name: String) -> Maybe<&2, String>:
  match as:
    case Nil{}:
      None{}
    case Con{Alias{+n, p}, rest}:
      +more = alias_path(rest, name)
      Bool.pick(Maybe<&2, String>, String.eq(n, name), Some{p}, more)

# a name in a law as a mention: `M.join` is `join` of what `M` imports; a
# plain name is of the law's own file
def mention(mm: Maybe<&2, String>, +file: String, +tt: String) -> Mention:
  match mm:
    case Some{p}:
      Mention{p, Bind.rest_of(String.to_list(tt))}
    case None{}:
      Mention{file, tt}

# every name among the tokens, as a mention
def mentions(toks: List<&2, Lex.Tok>, +as: List<&2, Alias>, +file: String) -> List<&2, Mention>:
  match toks:
    case Nil{}:
      Nil{}
    case Con{Lex.Tok{k, +t, l, c}, rest}:
      +more = mentions(rest, as, file)
      Lazy.stop(List<&2, Mention>, Bool.not(Lex.is_name(k)), more,
        _u => mention(alias_path(as, Bind.head_of(String.to_list(t))), file, t) <> more)

# the mentions of every quantified law of a tree: what its binders and its
# statement name. Its header, and so its own name, is not a mention, and a
# closed law names nothing (it covers one input, not the def)
def law_mentions(root: Tree.Node, +as: List<&2, Alias>, +file: String) -> List<&2, Mention>:
  match root:
    case Tree.NCons{Tree.Stmt{Tree.SLaw{}, kids, +body}, rest}:
      +more = law_mentions(rest, as, file)
      Lazy.stop(List<&2, Mention>, Bool.not(Closed.binds(body)), more,
        _u => List.append(&2, Mention, mentions(Tree.leaves(body), as, file), more))
    case Tree.NCons{h, rest}:
      law_mentions(rest, as, file)
    case other:
      Nil{}

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

# the top-level defs and types, by name and line: what the coverage rule grades
def top_items(items: List<&2, Outline.Item>) -> List<&2, Top>:
  match items:
    case Nil{}:
      Nil{}
    case Con{Outline.Item{Outline.IDef{}, name, line, sig, doc, path}, rest}:
      Top{Outline.IDef{}, name, line, []} <> top_items(rest)
    case Con{Outline.Item{Outline.IType{}, name, line, sig, doc, path}, +rest}:
      Top{Outline.IType{}, name, line, ctors(rest)} <> top_items(rest)
    case Con{other, rest}:
      top_items(rest)

# a law file or a test, by its path alone: not under law. Nothing the file's
# text mentions exempts it; IO is not an exemption, since an IO equality is a
# law.
def is_exempt(+pp: String) -> Bool:
  Bool.or(Paths.is_law_file(pp), Paths.is_test(pp))

# the significant tokens: no space, newline or comment
def significant(toks: List<&2, Lex.Tok>) -> List<&2, Lex.Tok>:
  match toks:
    case Nil{}:
      Nil{}
    case Con{Lex.Tok{+k, t, l, c}, rest}:
      +more = significant(rest)
      Bool.pick(List<&2, Lex.Tok>, Lex.significant(k), Lex.Tok{k, t, l, c} <> more, more)

# the name after `unsafe def`, when the tokens run so
def unsafe_name(toks: List<&2, Lex.Tok>) -> Maybe<&2, String>:
  match toks:
    case Con{Lex.Tok{k1, +u, l1, c1}, Con{Lex.Tok{k2, +d, l2, c2}, Con{Lex.Tok{k3, n, l3, c3}, rest}}}:
      Bool.pick(Maybe<&2, String>, Bool.and(String.eq(u, "unsafe"), String.eq(d, "def")), Some{n}, None{})
    case other:
      None{}

# an `@` that heads an unsafe def, onto the others
def push(mm: Maybe<&2, String>, +ll: U32, +cc: U32, more: List<&2, Unsafe>) -> List<&2, Unsafe>:
  match mm:
    case None{}:
      more
    case Some{n}:
      Unsafe{n, ll, cc} <> more

# every `@ unsafe def name` run of tokens, on one line or two
def unsafe_defs(toks: List<&2, Lex.Tok>) -> List<&2, Unsafe>:
  match toks:
    case Nil{}:
      Nil{}
    case Con{Lex.Tok{k, +at, +l, +c}, +rest}:
      +more = unsafe_defs(rest)
      Bool.pick(List<&2, Unsafe>, String.eq(at, "@"), push(unsafe_name(rest), l, c, more), more)

# the laws
# --------

# the doc of the item on a line; the items are in line order, so the search
# stops at it
def doc_at(items: List<&2, Outline.Item>, +at: U32) -> String:
  match items:
    case Nil{}:
      ""
    case Con{Outline.Item{kk, nn, +ln, sig, +doc, pp}, rest}:
      Lazy.stop(String, U32.is_le(at, ln), Bool.pick(String, U32.is_eq(ln, at), doc, ""), _u => doc_at(rest, at))

# every law of a tree, with whether it binds and its doc lines
def laws_of(root: Tree.Node, +items: List<&2, Outline.Item>) -> List<&2, Law>:
  match root:
    case Tree.NCons{Tree.Stmt{Tree.SLaw{}, +kids, body}, rest}:
      +at = Tree.line(kids)
      Law{Closed.name.of(Bind.declared(kids)), at, Closed.binds(body), String.lines(doc_at(items, at))}
        <> laws_of(rest, items)
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
def stated(is_laws: Bool, root: Tree.Node, as: List<&2, Alias>, file: String) -> List<&2, Mention>:
  match is_laws:
    case True{}:
      law_mentions(root, as, file)
    case False{}:
      Nil{}

# one parsed file read down to its digest
def of(s2: Src.Src) -> Digest:
  Src.Src{+path, text, toks, +tree, bound, +items} = s2
  +p = Imports.norm(path)
  Digest{path, p, Imports.dir_of(path), Paths.is_laws(path), Paths.is_law_file(path), is_exempt(p),
    top_items(items), stated(Paths.is_laws(path), tree, aliases(items, p), p), Imports.targets(items, p),
    unsafe_defs(significant(toks)), laws.in(Paths.is_laws(path), tree, items)}

# every file the linter read, in one pass, in order
def all(ss: List<&2, Src.Src>) -> List<&2, Digest>:
  match ss:
    case Nil{}:
      Nil{}
    case Con{s, rest}:
      of(s) <> all(rest)

# the import graph of the files, built once for every closure taken over it
def edges(ds: List<&2, Digest>) -> List<&2, Imports.Edge>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{Digest{path, norm, dir, is_laws, is_law_file, exempt, tops, says, deps, unsafes, laws}, rest}:
      Imports.Edge{norm, deps} <> edges(rest)
