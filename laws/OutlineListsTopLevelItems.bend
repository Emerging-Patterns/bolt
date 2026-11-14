# The outline lists every column-0 import, def, type, law and `@unsafe def`.
import Base
import ../src/syntax/lex.bend as Lex
import ../src/syntax/outline.bend as Outline
import ./defs/LineBreakChar.bend as D1

# the outline (laws/OutlineListsTopLevelItems.bend), written apart from outline.bend. A line starts
# inside a string when the line break before it sits in a string token: such
# a line is text, never an item. Any other line opens an item when it starts,
# at column 0, with `import `, `def `, `@unsafe def `, `law ` or `type `. An
# item is compared by its kind, name and line; its header, doc and path are
# left out, and so are the constructors of a type block, which are not
# column-0 items.

# one flag per line break in a text, in order, each str: whether the text is
# a string's
def top.breaks(tt: String, +str: Bool) -> List<&2, Bool>:
  match tt:
    case SNil{}:
      []
    case SCon{h, t}:
      +rest = top.breaks(t, str)
      Bool.pick(List<&2, Bool>, D1.breaks(h), str <> rest, rest)

# one flag per line break in the tokens' texts, in order: does it sit inside
# a string?
def top.strung(toks: List<&2, Lex.Tok>) -> List<&2, Bool>:
  match toks:
    case Nil{}:
      []
    case Con{Lex.Tok{k, t, _l, _c}, rest}:
      List.append(&2, Bool, top.breaks(t, Lex.is_str(k)), top.strung(rest))

# what ends a name: `(`, `<`, `:`, `{` or a space
def top.stop(+h: Char) -> Bool:
  Bool.or(Char.is_eq(h, '('),
    Bool.or(Char.is_eq(h, '<'),
      Bool.or(Char.is_eq(h, ':'),
        Bool.or(Char.is_eq(h, '{'), Char.is_eq(h, ' ')))))

# the name a header gives: its text up to the first char that ends a name
def top.name(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+h, t}:
      Bool.pick(String, top.stop(h), SNil{}, SCon{h, top.name(t)})

# a word is not empty
def top.word(s: String) -> Bool:
  Bool.not(String.is_empty(s))

# an import line, by its words: named by its fourth, the alias of `import P
# as A`, when it has four or more; by its path when it has two; else no item
# (bend reads no other shape)
def top.import(ws: List<&2, String>, n: U32) -> Maybe<&2, Outline.Item>:
  match ws:
    case Con{_i, Con{_p, Con{_a, Con{alias, _r}}}}:
      Some{Outline.Item{Outline.IImport{}, alias, n, "", "", ""}}
    case Con{_i, Con{path, Nil{}}}:
      Some{Outline.Item{Outline.IImport{}, path, n, "", "", ""}}
    case _other:
      None{}

# the item a line of code opens at column 0, by its kind, name and line nn
def top.head(+s: String, +nn: U32) -> Maybe<&2, Outline.Item>:
  Bool.pick(Maybe<&2, Outline.Item>, String.starts_with(s, "import "),
    top.import(List.filter(~String, ~top.word, String.split(s, ' ')), nn),
  Bool.pick(Maybe<&2, Outline.Item>, String.starts_with(s, "def "),
    Some{Outline.Item{Outline.IDef{}, top.name(String.drop(s, 4n)), nn, "", "", ""}},
  Bool.pick(Maybe<&2, Outline.Item>, String.starts_with(s, "@unsafe def "),
    Some{Outline.Item{Outline.IDef{}, top.name(String.drop(s, 12n)), nn, "", "", ""}},
  Bool.pick(Maybe<&2, Outline.Item>, String.starts_with(s, "law "),
    Some{Outline.Item{Outline.ILaw{}, top.name(String.drop(s, 4n)), nn, "", "", ""}},
  Bool.pick(Maybe<&2, Outline.Item>, String.starts_with(s, "type "),
    Some{Outline.Item{Outline.IType{}, top.name(String.drop(s, 5n)), nn, "", "", ""}},
    None{})))))

# an item onto the items, when there is one
def top.put(m: Maybe<&2, Outline.Item>, rest: List<&2, Outline.Item>) -> List<&2, Outline.Item>:
  match m:
    case None{}:
      rest
    case Some{item}:
      item <> rest

# the first line's flag; no flag left is no
def top.first(ins: List<&2, Bool>) -> Bool:
  match ins:
    case Nil{}:
      False{}
    case Con{h, _t}:
      h

# the flags of the lines after the first
def top.later(ins: List<&2, Bool>) -> List<&2, Bool>:
  match ins:
    case Nil{}:
      []
    case Con{_h, t}:
      t

# the items the lines open, the first numbered n; ins flags the lines that
# start inside a string, which open none
def top.spec(lines: List<&2, String>, +ins: List<&2, Bool>, +n: U32) -> List<&2, Outline.Item>:
  match lines:
    case Nil{}:
      []
    case Con{l, rest}:
      top.put(Bool.pick(Maybe<&2, Outline.Item>, top.first(ins), None{}, top.head(l, n)),
        top.spec(rest, top.later(ins), (n + 1 : U32)))

# every kind but a constructor
def top.kept(k: Outline.ItemKind) -> Bool:
  match k:
    case Outline.ICtor{}:
      False{}
    case other:
      True{}

# an item by its kind, name and line, onto the rest; a constructor is left out
def top.key(item: Outline.Item, +rest: List<&2, Outline.Item>) -> List<&2, Outline.Item>:
  match item:
    case Outline.Item{+k, nm, ln, _s, _d, _p}:
      Bool.pick(List<&2, Outline.Item>, top.kept(k), Outline.Item{k, nm, ln, "", "", ""} <> rest, rest)

# the items by kind, name and line, constructors left out
def top.keys(items: List<&2, Outline.Item>) -> List<&2, Outline.Item>:
  match items:
    case Nil{}:
      []
    case Con{h, t}:
      top.key(h, top.keys(t))

# LAW: the outline lists exactly the column-0 imports, defs, `@unsafe def`s,
# laws and types, in order, each with its name and line: whatever the text
# and its tokens, line 0 starts outside any string, and the line after each
# line break starts inside one exactly when that break sits in a string token
law outline:
  for +text: String
  for +toks: List<&2, Lex.Tok>
  {top.keys(Outline.of_tokens(text, toks))
    == top.spec(String.lines(text), False{} <> top.strung(toks), 0) : List<&2, Outline.Item>}

# LAW: a comment line that opens with `# ` is its text after those two chars
law undoc_drops_hash_and_space:
  for +s: String
  for e: {String.starts_with(s, "# ") == True{} : Bool}
  {Outline.undoc(s) == String.drop(s, 2n) : String}

# LAW: one that opens with a bare `#` is its text after it
law undoc_drops_a_bare_hash:
  for +s: String
  for e1: {String.starts_with(s, "# ") == False{} : Bool}
  for e2: {String.starts_with(s, "#") == True{} : Bool}
  {Outline.undoc(s) == String.drop(s, 1n) : String}

# LAW: a line that is no comment is left as it is
law undoc_keeps_other_lines:
  for +s: String
  for e1: {String.starts_with(s, "# ") == False{} : Bool}
  for e2: {String.starts_with(s, "#") == False{} : Bool}
  {Outline.undoc(s) == s : String}

# LAW: an item's doc is its comment lines, each without its `# `, one a line
law doc_text_joins_lines:
  for doc: List<&2, String>
  {Outline.doc_text(doc) == String.join(Outline.undoc.all(doc, []), "\n") : String}

# LAW: a header that runs over several lines is those lines in order, one a
# line
law sig_text_joins_lines:
  for sig: List<&2, String>
  {Outline.sig_text(sig) == String.join(List.reverse(&2, String, sig), "\n") : String}
