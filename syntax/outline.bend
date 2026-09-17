# syntax/outline: a source's top-level items, read line by line. A top-level
# item starts at column 0, so a line the outline does not understand costs
# nothing: it is skipped, and the items around it still stand. That tolerance
# is the point: an editor asks about files that are half-written.
import Base

type ItemKind is Data:
  IImport{}
  IDef{}
  ILaw{}
  IType{}
  ICtor{}
  ILocal{}

# line is 0-based; sig is the header text (a def's through its `:`, a law's
# whole block, a constructor's line); doc is the comment block right above;
# path is an import's target
type Item is Data:
  Item{kind: ItemKind, name: String, line: U32, sig: String, doc: String, path: String}

type Cls is Data:
  LBlank{}
  LComment{text: String}
  LIndent{text: String}
  LImport{}
  LDef{}
  LLaw{}
  LType{}
  LOther{}

# Pending: a def's header that has not reached its `:`, or a law's block
type Mode is Data:
  Top{}
  InType{}
  Pending{kind: ItemKind, name: String, line: U32, doc: String, sig: List<&2, String>}

# doc and out are reversed
type St is Data:
  St{mode: Mode, n: U32, doc: List<&2, String>, out: List<&2, Item>}

def is_blank(s: String) -> Bool:
  List.all(~&2, ~Char, ~Char.is_space, String.to_list(s))

def classify(+s: String) -> Cls:
  Bool.pick(Cls, is_blank(s), LBlank{},
    Bool.pick(Cls, String.starts_with(s, "#"), LComment{s},
      Bool.pick(Cls, String.starts_with(s, " "), LIndent{s},
        Bool.pick(Cls, String.starts_with(s, "import "), LImport{},
          Bool.pick(Cls, Bool.or(String.starts_with(s, "def "), String.starts_with(s, "@unsafe def ")), LDef{},
            Bool.pick(Cls, String.starts_with(s, "law "), LLaw{},
              Bool.pick(Cls, String.starts_with(s, "type "), LType{}, LOther{})))))))

# a name runs to the first of ( < : { or a space
def name.go(cs: List<&2, Char>, acc: List<&2, Char>) -> List<&2, Char>:
  match cs:
    case Con{'(', t}:
      acc
    case Con{'<', t}:
      acc
    case Con{':', t}:
      acc
    case Con{'{', t}:
      acc
    case Con{' ', t}:
      acc
    case Con{c, t}:
      name.go(t, c <> acc)
    case Nil{}:
      acc

def name(s: String) -> String:
  String.from_list(List.reverse(&2, Char, name.go(String.to_list(s), [])))

def lstrip.go(cs: List<&2, Char>) -> List<&2, Char>:
  match cs:
    case Con{' ', t}:
      lstrip.go(t)
    case other:
      other

def lstrip(s: String) -> String:
  String.from_list(lstrip.go(String.to_list(s)))

def nonempty(s: String) -> Bool:
  Bool.not(String.is_empty(s))

# the words of a line
def words(s: String) -> List<&2, String>:
  List.filter(~String, ~nonempty, String.split(s, ' '))

# a comment line without its `# `
def undoc(+s: String) -> String:
  Bool.pick(String, String.starts_with(s, "# "), String.drop(s, 2n),
    Bool.pick(String, String.starts_with(s, "#"), String.drop(s, 1n), s))

def undoc.all(doc: List<&2, String>, acc: List<&2, String>) -> List<&2, String>:
  match doc:
    case Nil{}:
      acc
    case Con{h, t}:
      undoc.all(t, undoc(h) <> acc)

# the comment block (reversed) as text
def doc_text(doc: List<&2, String>) -> String:
  String.join(undoc.all(doc, []), "\n")

def sig_text(sig: List<&2, String>) -> String:
  String.join(List.reverse(&2, String, sig), "\n")

def add(m: Maybe<&2, Item>, out: List<&2, Item>) -> List<&2, Item>:
  match m:
    case None{}:
      out
    case Some{item}:
      item <> out

# `import <path> as <Alias>` is named by its alias; `import Base` by its path
def import_item.of(ws: List<&2, String>, s: String, n: U32, doc: String) -> Maybe<&2, Item>:
  match ws:
    case Con{i, Con{path, Con{as, Con{alias, r}}}}:
      Some{Item{IImport{}, alias, n, s, doc, path}}
    case Con{i, Con{+path, Nil{}}}:
      Some{Item{IImport{}, path, n, s, doc, path}}
    case other:
      None{}

def import_item(+s: String, n: U32, doc: String) -> Maybe<&2, Item>:
  import_item.of(words(s), s, n, doc)

def def_name(+s: String) -> String:
  name(Bool.pick(String, String.starts_with(s, "@"), String.drop(s, 12n), String.drop(s, 4n)))

def starts_upper.of(cs: List<&2, Char>) -> Bool:
  match cs:
    case Con{c, t}:
      Char.is_upper(c)
    case Nil{}:
      False{}

def starts_upper(s: String) -> Bool:
  starts_upper.of(String.to_list(s))

# an indented line of a type block: `Ctor{..}`
def ctor.of(+t: String, n: U32) -> Maybe<&2, Item>:
  Bool.pick(Maybe<&2, Item>, Bool.and(starts_upper(t), String.contains(t, "{")),
    Some{Item{ICtor{}, name(t), n, t, "", ""}}, None{})

def ctor(text: String, n: U32) -> Maybe<&2, Item>:
  ctor.of(lstrip(text), n)

def is_def(k: ItemKind) -> Bool:
  match k:
    case IDef{}:
      True{}
    case other:
      False{}

# what was pending becomes an item
def flush(mode: Mode, out: List<&2, Item>) -> List<&2, Item>:
  match mode:
    case Pending{k, nm, l, d, sig}:
      Item{k, nm, l, sig_text(sig), d, ""} <> out
    case other:
      out

# one more line of a pending header; a def's ends at the line that ends in `:`
def pend_more(+k: ItemKind, +nm: String, +l: U32, +d: String, +sig: List<&2, String>, +text: String, +n: U32,
  +out: List<&2, Item>) -> St:
  Bool.pick(St, Bool.and(is_def(k), String.ends_with(text, ":")),
    St{Top{}, (n + 1 : U32), [], Item{k, nm, l, sig_text(text <> sig), d, ""} <> out},
    St{Pending{k, nm, l, d, text <> sig}, (n + 1 : U32), [], out})

def indent(mode: Mode, text: String, +n: U32, out: List<&2, Item>) -> St:
  match mode:
    case Pending{k, nm, l, d, sig}:
      pend_more(k, nm, l, d, sig, text, n, out)
    case InType{}:
      St{InType{}, (n + 1 : U32), [], add(ctor(text, n), out)}
    case Top{}:
      St{Top{}, (n + 1 : U32), [], out}

# a column-0 line that starts nothing: `) -> T:` closing a def's header that
# broke across lines; anywhere else it is junk, and ends what was pending
def stray(+mode: Mode, text: String, +n: U32, +out: List<&2, Item>) -> St:
  match mode:
    case Pending{IDef{}, nm, l, d, sig}:
      pend_more(IDef{}, nm, l, d, sig, text, n, out)
    case m:
      St{Top{}, (n + 1 : U32), [], flush(m, out)}

def start_def(+s: String, +n: U32, +doc: String, +out: List<&2, Item>) -> St:
  Bool.pick(St, String.ends_with(s, ":"),
    St{Top{}, (n + 1 : U32), [], Item{IDef{}, def_name(s), n, s, doc, ""} <> out},
    St{Pending{IDef{}, def_name(s), n, doc, [s]}, (n + 1 : U32), [], out})

# a comment continues the block above it only at the top level
def doc_above(mode: Mode, doc: List<&2, String>) -> List<&2, String>:
  match mode:
    case Top{}:
      doc
    case other:
      []

def step.go(cls: Cls, +mode: Mode, +s: String, +n: U32, doc: List<&2, String>, out: List<&2, Item>) -> St:
  match cls:
    case LBlank{}:
      St{Top{}, (n + 1 : U32), [], flush(mode, out)}
    case LComment{t}:
      St{Top{}, (n + 1 : U32), t <> doc_above(mode, doc), flush(mode, out)}
    case LIndent{t}:
      indent(mode, t, n, out)
    case LImport{}:
      St{Top{}, (n + 1 : U32), [], add(import_item(s, n, doc_text(doc)), flush(mode, out))}
    case LDef{}:
      start_def(s, n, doc_text(doc), flush(mode, out))
    case LLaw{}:
      St{Pending{ILaw{}, name(String.drop(s, 4n)), n, doc_text(doc), [s]}, (n + 1 : U32), [], flush(mode, out)}
    case LType{}:
      St{InType{}, (n + 1 : U32), [], Item{IType{}, name(String.drop(s, 5n)), n, s, doc_text(doc), ""} <> flush(mode, out)}
    case LOther{}:
      stray(mode, s, n, out)

def step(+s: String, st: St) -> St:
  St{mode, n, doc, out} = st
  step.go(classify(s), mode, s, n, doc, out)

def run(lines: List<&2, String>, st: St) -> St:
  match lines:
    case Nil{}:
      st
    case Con{l, t}:
      run(t, step(l, st))

def finish(st: St) -> List<&2, Item>:
  St{mode, n, doc, out} = st
  List.reverse(&2, Item, flush(mode, out))

def items(text: String) -> List<&2, Item>:
  finish(run(String.lines(text), St{Top{}, 0, [], []}))

# lookups
# -------

def is_import(k: ItemKind) -> Bool:
  match k:
    case IImport{}:
      True{}
    case other:
      False{}

# the item of that name; imports are not names of the module
def find(items: List<&2, Item>, +name: String) -> Maybe<&2, Item>:
  match items:
    case Nil{}:
      None{}
    case Con{Item{+k, +nm, l, s, d, p}, t}:
      Bool.pick(Maybe<&2, Item>, Bool.and(Bool.not(is_import(k)), String.eq(nm, name)),
        Some{Item{k, nm, l, s, d, p}}, find(t, name))

# the path behind an import alias
def import_path(items: List<&2, Item>, +alias: String) -> Maybe<&2, String>:
  match items:
    case Nil{}:
      None{}
    case Con{Item{k, nm, l, s, d, p}, t}:
      Bool.pick(Maybe<&2, String>, Bool.and(is_import(k), String.eq(nm, alias)),
        Some{p}, import_path(t, alias))

def has(names: List<&2, String>, +name: String) -> Bool:
  match names:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.or(String.eq(h, name), has(t, name))

def starting.go(items: List<&2, Item>, +prefix: String, +qual: String, +seen: List<&2, String>) -> List<&2, Item>:
  match items:
    case Nil{}:
      Nil{}
    case Con{Item{+k, +nm, l, s, d, p}, t}:
      +take = Bool.and(Bool.and(Bool.not(is_import(k)), String.starts_with(nm, prefix)), Bool.not(has(seen, nm)))
      # one recursive call: Bool.pick evaluates both of its branches
      +rest = starting.go(t, prefix, qual, Bool.pick(List<&2, String>, take, nm <> seen, seen))
      Bool.pick(List<&2, Item>, take, Item{k, qual ++ nm, l, s, d, p} <> rest, rest)

# the named items whose name starts with prefix, each renamed qual ++ name (the
# text to insert). A law and the def that fills it share a name: the first
# stands for both.
def starting(items: List<&2, Item>, prefix: String, qual: String) -> List<&2, Item>:
  starting.go(items, prefix, qual, [])

# the import aliases that start with prefix (`import Base` has none)
def aliases(items: List<&2, Item>, +prefix: String) -> List<&2, Item>:
  match items:
    case Nil{}:
      Nil{}
    case Con{Item{+k, +nm, l, s, d, +p}, t}:
      +rest = aliases(t, prefix)
      Bool.pick(List<&2, Item>,
        Bool.and(Bool.and(is_import(k), String.starts_with(nm, prefix)), Bool.not(String.eq(nm, p))),
        Item{k, nm, l, s, d, p} <> rest, rest)
