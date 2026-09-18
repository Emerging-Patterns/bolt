# rule law (project-wide): in a project that states laws (a directory with a
# LAWS.bend), every pure def is named by some law. A def a law never mentions
# has no stated property: it is the coverage gap. A type is covered once any
# law reaches its module (a law about an instance names the accessors, never
# the service type). Out of scope: helpers (dotted names), `main`, tests, the
# law files themselves, and a module that touches IO (a law cannot state it).
import Base
import ../finding.bend as F
import ../file.bend as File
import ../../syntax/lex.bend as Lex
import ../../syntax/tree.bend as Tree
import ../../syntax/bind.bend as Bind
import ../../syntax/outline.bend as Outline

# paths
# -----

# a segment onto the reversed path: `.` and empty are dropped, `..` pops
def norm.put(+s: String, acc: List<&2, String>) -> List<&2, String>:
  match acc:
    case Con{+h, +t}:
      Bool.pick(List<&2, String>, String.eq(s, ".."), t,
        Bool.pick(List<&2, String>, Bool.or(String.eq(s, "."), String.is_empty(s)), h <> t, s <> (h <> t)))
    case Nil{}:
      Bool.pick(List<&2, String>, Bool.or(String.eq(s, ".."), Bool.or(String.eq(s, "."), String.is_empty(s))),
        [], [s])

def norm.go(segs: List<&2, String>, acc: List<&2, String>) -> List<&2, String>:
  match segs:
    case Nil{}:
      List.reverse(&2, String, acc)
    case Con{+s, rest}:
      norm.go(rest, norm.put(s, acc))

# a path without `./`, `../` and doubled slashes, so two spellings compare
def norm(path: String) -> String:
  String.join(norm.go(String.split(path, '/'), []), "/")

# the segments but the last
def init(segs: List<&2, String>) -> List<&2, String>:
  match segs:
    case Nil{}:
      Nil{}
    case Con{h, Nil{}}:
      Nil{}
    case Con{h, t}:
      h <> init(t)

# a path's directory, with its slash (`wire/monoid/`; `` at the root)
def dir_of(path: String) -> String:
  +segs = init(String.split(norm(path), '/'))
  Bool.pick(String, Nat.is_eq(List.length(&2, String, segs), 0n), "", String.join(segs, "/") ++ "/")

# a path imported from a file, normalized
def resolve(+from: String, rel: String) -> String:
  norm(dir_of(from) ++ rel)

# what the laws name
# ------------------

# an import alias and the path it names
type Alias is Data:
  Alias{name: String, path: String}

# a law names an item of a module (a type is covered by any mention of its module)
type Mention is Data:
  Mention{path: String, name: String}

# the aliases a file imports
def aliases(items: List<&2, Outline.Item>, +from: String) -> List<&2, Alias>:
  match items:
    case Nil{}:
      Nil{}
    case Con{Outline.Item{Outline.IImport{}, name, line, sig, doc, path}, rest}:
      Alias{name, resolve(from, path)} <> aliases(rest, from)
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
def mention(m: Maybe<&2, String>, +file: String, +t: String) -> Mention:
  match m:
    case Some{p}:
      Mention{p, Bind.rest_of(String.to_list(t))}
    case None{}:
      Mention{file, t}

# every name among the tokens, as a mention
def mentions(toks: List<&2, Lex.Tok>, +as: List<&2, Alias>, +file: String) -> List<&2, Mention>:
  match toks:
    case Nil{}:
      Nil{}
    case Con{Lex.Tok{k, +t, l, c}, rest}:
      +more = mentions(rest, as, file)
      Bool.pick(List<&2, Mention>, Lex.is_name(k),
        mention(alias_path(as, Bind.head_of(String.to_list(t))), file, t) <> more, more)

# the mentions of every law statement of a tree
def laws(root: Tree.Node, +as: List<&2, Alias>, +file: String) -> List<&2, Mention>:
  match root:
    case Tree.NCons{Tree.Stmt{Tree.SLaw{}, kids, body}, rest}:
      List.concat(&2, Mention, [mentions(Tree.leaves(kids), as, file), mentions(Tree.leaves(body), as, file),
        laws(rest, as, file)])
    case Tree.NCons{h, rest}:
      laws(rest, as, file)
    case other:
      Nil{}

# what the laws of every file name
def named(files: List<&2, File.File>) -> List<&2, Mention>:
  match files:
    case Nil{}:
      Nil{}
    case Con{File.File{+path, +text}, rest}:
      +file = norm(path)
      List.concat(&2, Mention, [laws(Tree.parse(text), aliases(Outline.items(text), file), file), named(rest)])

# is the item named?
def has_item(ms: List<&2, Mention>, +p: String, +name: String) -> Bool:
  match ms:
    case Nil{}:
      False{}
    case Con{Mention{+mp, +mn}, rest}:
      Bool.or(Bool.and(String.eq(mp, p), String.eq(mn, name)), has_item(rest, p, name))

# is anything of the module named?
def has_module(ms: List<&2, Mention>, +p: String) -> Bool:
  match ms:
    case Nil{}:
      False{}
    case Con{Mention{+mp, mn}, rest}:
      Bool.or(String.eq(mp, p), has_module(rest, p))

# what is in scope
# ----------------

# the directories that state laws
def law_dirs(files: List<&2, File.File>) -> List<&2, String>:
  match files:
    case Nil{}:
      Nil{}
    case Con{File.File{+path, text}, rest}:
      +more = law_dirs(rest)
      Bool.pick(List<&2, String>, String.ends_with(path, "LAWS.bend"), dir_of(path) <> more, more)

# is the path under one of the directories?
def under(dirs: List<&2, String>, +p: String) -> Bool:
  match dirs:
    case Nil{}:
      False{}
    case Con{d, rest}:
      Bool.or(String.starts_with(p, d), under(rest, p))

# a law file, a test, or a module that touches IO: not under law
def exempt(+p: String, text: String) -> Bool:
  Bool.or(Bool.or(String.ends_with(p, "LAWS.bend"), String.ends_with(p, "PROOF.bend")),
    Bool.or(String.contains(p, "tests/"), String.contains(text, "IO")))

# a def or a type that no law reaches
def gaps(items: List<&2, Outline.Item>, +ms: List<&2, Mention>, +p: String, +path: String) -> List<&2, F.Finding>:
  match items:
    case Nil{}:
      Nil{}
    case Con{Outline.Item{Outline.IDef{}, +name, +line, sig, doc, ipath}, rest}:
      +more = gaps(rest, ms, p, path)
      Bool.pick(List<&2, F.Finding>,
        Bool.or(Bool.or(String.contains(name, "."), String.eq(name, "main")), has_item(ms, p, name)), more,
        F.Finding{path, line, 0, 0, "law", "def " ++ name ++ " is named by no law"} <> more)
    case Con{Outline.Item{Outline.IType{}, +name, +line, sig, doc, ipath}, rest}:
      +more = gaps(rest, ms, p, path)
      Bool.pick(List<&2, F.Finding>, has_module(ms, p), more,
        F.Finding{path, line, 0, 0, "law", "type " ++ name ++ ": no law reaches this module"} <> more)
    case Con{other, rest}:
      gaps(rest, ms, p, path)

# every file in scope, against what the laws name
def check.go(files: List<&2, File.File>, +dirs: List<&2, String>, +ms: List<&2, Mention>) -> List<&2, F.Finding>:
  match files:
    case Nil{}:
      Nil{}
    case Con{File.File{+path, +text}, rest}:
      +p = norm(path)
      +more = check.go(rest, dirs, ms)
      Bool.pick(List<&2, F.Finding>, Bool.and(under(dirs, p), Bool.not(exempt(p, text))),
        List.concat(&2, F.Finding, [gaps(Outline.items(text), ms, p, path), more]), more)

# the rule, over every file the linter read
def check(+files: List<&2, File.File>) -> List<&2, F.Finding>:
  check.go(files, law_dirs(files), named(files))
