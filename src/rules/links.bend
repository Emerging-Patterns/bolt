# src/rules/links: what a file's imports are to it, read once for the
# project rule `spare` (rules/suspicious/spare.bend) and kept in the file's
# digest (rules/digest.bend). Two things: the imports whose alias the file
# never names, and whether importing the file does something besides making
# its names available.
#
# An import is named by its alias (`import ./ops.bend as O`); the file names
# the alias when a dotted name outside an import line starts with it and a
# dot (`O.add`, `O.Shape{..}`, `def O.lemma(..)`). A comment or a string is
# no name, and an import line's own path is none either (`./O.bend`).
#
# A file loads when it states a law, holds a def that is a proof (one that
# returns `-> {..}`, or has no type: rules/calls.bend's `proof`), or holds a
# foreign def (one whose body opens with `import`). `bend` checks a law and
# a proof with whatever imports their file, and links a foreign def only
# when the entry reaches its file, so an import of such a file has a use
# though nothing names its alias. Pure.
import Base
import ../syntax/lex.bend as Lex
import ../syntax/tree.bend as Tree
import ../syntax/outline.bend as Outline
import ../lazy/lazy.bend as Lazy
import ./imports.bend as Imports
import ./calls.bend as Calls
import ./suspicious/unused.bend as Unused

# an import the file never names: its alias, the file it names (resolved
# against the importer and normalized) and the line it is on
type Spare is Data:
  Spare{alias: String, path: String, line: U32}

# a file's links: whether it loads, and its spare imports
type Links is Data:
  Links{loads: Bool, spare: List<&2, Spare>}

# is the token a dotted name that starts with the prefix (an alias and a
# dot)?
def dotted(k: Lex.TokKind, t: String, prefix: String) -> Bool:
  match k:
    case Lex.TDotted{}:
      String.starts_with(t, prefix)
    case _other:
      False{}

# is the token the keyword `import`?
def opens(k: Lex.TokKind, t: String) -> Bool:
  match k:
    case Lex.TKey{}:
      String.eq(t, "import")
    case _other:
      False{}

# is the walk still on an import line past this token: one it was on that
# has not ended, or one this token opens?
def skips(+k: Lex.TokKind, t: String, skip: Bool) -> Bool:
  Bool.or(Bool.and(skip, Bool.not(Lex.is_nl(k))), opens(k, t))

# does a dotted name among the tokens, outside every import line, start
# with the prefix? skip: the walk is on an import line; hit: a token before
# these was such a name, so the answer is known
def names.go(toks: List<&2, Lex.Tok>, +prefix: String, skip: Bool, hit: Bool) -> Bool:
  match toks hit:
    case _ts True{}:
      True{}
    case Nil{} False{}:
      False{}
    case Con{Lex.Tok{+k, +t, _l, _c}, rest} False{}:
      +on = skips(k, t, skip)
      names.go(rest, prefix, on, Bool.and(Bool.not(on), dotted(k, t, prefix)))

# does the file name the alias: a dotted name outside its import lines that
# starts with the alias and a dot?
def names(toks: List<&2, Lex.Tok>, alias: String) -> Bool:
  names.go(toks, alias ++ ".", False{}, False{})

# is an import one of a file by a relative path, under an alias of its own
# (`import Base` is named by its path, and a hub package's path is not
# relative)?
def local(name: String, +path: String) -> Bool:
  Bool.and(Bool.not(String.eq(name, path)), String.starts_with(path, "."))

# the imports of files by relative paths whose alias the tokens never name,
# in order
def spares(items: List<&2, Outline.Item>, +toks: List<&2, Lex.Tok>, +from: String) -> List<&2, Spare>:
  match items:
    case Nil{}:
      Nil{}
    case Con{Outline.Item{Outline.IImport{}, +name, line, _sig, _doc, +path}, rest}:
      +more = spares(rest, toks, from)
      Bool.pick(List<&2, Spare>, Lazy.and_then(local(name, path), _u => Bool.not(names(toks, name))),
        Spare{name, Imports.resolve(from, path), line} <> more, more)
    case Con{_other, rest}:
      spares(rest, toks, from)

# does the file name the alias of any import of its own?
def uses(items: List<&2, Outline.Item>, +toks: List<&2, Lex.Tok>) -> Bool:
  match items:
    case Nil{}:
      False{}
    case Con{Outline.Item{Outline.IImport{}, +name, _line, _sig, _doc, path}, rest}:
      Lazy.or_else(Lazy.and_then(Bool.not(String.eq(name, path)), _u => names(toks, name)), _v => uses(rest, toks))
    case Con{_other, rest}:
      uses(rest, toks)

# a file's spare imports: those it never names, when it names another. A
# file that names none of its imports loads them (an entry, a harness, a
# list of what a package publishes); it has no leftover among them
def spare(+items: List<&2, Outline.Item>, +toks: List<&2, Lex.Tok>, from: String) -> List<&2, Spare>:
  Lazy.stop(List<&2, Spare>, Bool.not(uses(items, toks)), [], _u => spares(items, toks, from))

# does a def load: is it a proof, or foreign?
def loads.def(+kids: Tree.Node, +body: Tree.Node) -> Bool:
  Bool.or(Calls.proof(Calls.header(kids, body)), Unused.foreign.opens(Calls.under(kids, body)))

# does the file load: a law, a def that is a proof, or a foreign def among
# its top-level statements?
def loads(root: Tree.Node) -> Bool:
  match root:
    case Tree.NCons{Tree.Stmt{Tree.SLaw{}, _kids, _body}, _rest}:
      True{}
    case Tree.NCons{Tree.Stmt{Tree.SDef{}, kids, body}, rest}:
      Lazy.or_else(loads.def(kids, body), _u => loads(rest))
    case Tree.NCons{_h, rest}:
      loads(rest)
    case _other:
      False{}

# a parsed file's links, its path normalized already
def of(items: List<&2, Outline.Item>, toks: List<&2, Lex.Tok>, tree: Tree.Node, from: String) -> Links:
  Links{loads(tree), spare(items, toks, from)}
