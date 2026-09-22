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

# what a file holds
# -----------------

# a law names an item of a module (a type is covered by any mention of its module)
type Mention is Data:
  Mention{path: String, name: String}

# a top-level def or type, by kind, name and the line it starts on
type Top is Data:
  Top{kind: Outline.ItemKind, name: String, line: U32}

# an `@unsafe def` and where its `@` is
type Unsafe is Data:
  Unsafe{name: String, line: U32, col: U32}

# one file as the project rules see it: its path as given and normalized, its
# directory, whether it states laws (LAWS.bend) or proves them too
# (PROOF.bend), whether the law rule lets it off, its top-level items, what
# its own laws name, the files it imports, and its `@unsafe` defs
type Digest is Data:
  Digest{path: String, norm: String, dir: String, is_laws: Bool, is_law_file: Bool, exempt: Bool,
    tops: List<&2, Top>, says: List<&2, Mention>, deps: List<&2, String>, unsafes: List<&2, Unsafe>}

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

# the mentions of every law statement of a tree
def law_mentions(root: Tree.Node, +as: List<&2, Alias>, +file: String) -> List<&2, Mention>:
  match root:
    case Tree.NCons{Tree.Stmt{Tree.SLaw{}, kids, body}, rest}:
      List.concat(&2, Mention, [mentions(Tree.leaves(kids), as, file), mentions(Tree.leaves(body), as, file),
        law_mentions(rest, as, file)])
    case Tree.NCons{h, rest}:
      law_mentions(rest, as, file)
    case other:
      Nil{}

# what the file holds besides
# ---------------------------

# the top-level defs and types, by name and line: what the law rule grades
def top_items(items: List<&2, Outline.Item>) -> List<&2, Top>:
  match items:
    case Nil{}:
      Nil{}
    case Con{Outline.Item{Outline.IDef{}, name, line, sig, doc, path}, rest}:
      Top{Outline.IDef{}, name, line} <> top_items(rest)
    case Con{Outline.Item{Outline.IType{}, name, line, sig, doc, path}, rest}:
      Top{Outline.IType{}, name, line} <> top_items(rest)
    case Con{other, rest}:
      top_items(rest)

# a law file or a test: not under law. IO in the file is not an exemption:
# an IO equality is a law.
def is_exempt(+pp: String) -> Bool:
  Bool.or(Bool.or(String.ends_with(pp, "LAWS.bend"), String.ends_with(pp, "PROOF.bend")),
    String.contains(pp, "tests/"))

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

# the digest
# ----------

# one parsed file read down to its digest
def of(s2: Src.Src) -> Digest:
  Src.Src{+path, text, toks, tree, bound, +items} = s2
  +p = Imports.norm(path)
  Digest{path, p, Imports.dir_of(path), String.ends_with(path, "LAWS.bend"),
    Bool.or(String.ends_with(path, "LAWS.bend"), String.ends_with(path, "PROOF.bend")), is_exempt(p),
    top_items(items), law_mentions(tree, aliases(items, p), p), Imports.targets(items, p),
    unsafe_defs(significant(toks))}

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
    case Con{Digest{path, norm, dir, is_laws, is_law_file, exempt, tops, says, deps, unsafes}, rest}:
      Imports.Edge{norm, deps} <> edges(rest)
